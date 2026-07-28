#!/usr/bin/env python3
"""台股籌碼資料每日收集（開放授權來源）——**零第三方相依，純標準庫**。

這支是「公開資料 repo」的唯一程式。設計上刻意與私有 App 分離，理由有三：

1. **授權**：只收 openapi 開放授權來源。個人模式限定的 rwd 端點**在此完全不存在**，
   所以結構上不可能把不可散布的資料寫進公開 repo —— 不必依賴人記得檢查。
2. **安全**：不需要任何憑證或 token（openapi 匿名可取），CI 也不需要 `pip install`
   （純標準庫），供應鏈攻擊面歸零。
3. **成本**：public repo 的 GitHub Actions 免費無限，不會再吃掉私人額度。

輸出格式與私有 App 的歷史庫一致，兩邊資料可互通。

用法::

    python harvest.py                 # 收集今天，寫入 ./data
    python harvest.py --dir /path     # 指定輸出目錄
    python harvest.py --status        # 只看累積狀況

資料來源與授權
--------------
- 臺灣證券交易所 OpenAPI（https://openapi.twse.com.tw）
- 證券櫃檯買賣中心 OpenAPI（https://www.tpex.org.tw/openapi）
兩者皆為政府資料開放授權（https://data.gov.tw/license）。使用時請保留出處標示。
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import ssl
import sys
import urllib.request
from datetime import date, datetime, timezone
from http.client import HTTPException
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import urlsplit

SCHEMA_VERSION = 1
DIRNAME = "official"
LICENSE_OPEN = "open"          # 本檔**只會**產生 open；personal 來源在此不存在
ATTRIBUTION = {
    "twse": "資料來源：臺灣證券交易所",
    "tpex": "資料來源：證券櫃檯買賣中心",
}

# --- 端點（主機白名單就是這兩個，不接受任何其他來源）-------------------------
TWSE_HOST = "openapi.twse.com.tw"
TPEX_HOST = "www.tpex.org.tw"
ALLOWED_HOSTS = frozenset({TWSE_HOST, TPEX_HOST})

U_TWSE_MARGIN = f"https://{TWSE_HOST}/v1/exchangeReport/MI_MARGN"
U_TWSE_PRICE = f"https://{TWSE_HOST}/v1/exchangeReport/STOCK_DAY_ALL"
U_TPEX_MARGIN = f"https://{TPEX_HOST}/openapi/v1/tpex_mainboard_margin_balance"
U_TPEX_INST = f"https://{TPEX_HOST}/openapi/v1/tpex_3insti_daily_trading"
U_TPEX_PRICE = f"https://{TPEX_HOST}/openapi/v1/tpex_mainboard_quotes"

MAX_BYTES = 8_000_000
TIMEOUT = 30.0

KIND_FIELDS: dict[str, tuple[str, ...]] = {
    "margin_twse": ("margin_balance_lots", "short_balance_lots"),
    "margin_tpex": ("margin_balance_lots", "short_balance_lots"),
    "inst_tpex": ("foreign_net", "trust_net", "dealer_net", "total_net"),
    "price_twse": ("open", "high", "low", "close", "volume_shares"),
    "price_tpex": ("open", "high", "low", "close", "volume_shares"),
}
VALUE_INT, VALUE_DECIMAL = "int", "decimal"
KIND_VALUE_TYPE = {
    "margin_twse": VALUE_INT, "margin_tpex": VALUE_INT, "inst_tpex": VALUE_INT,
    "price_twse": VALUE_DECIMAL, "price_tpex": VALUE_DECIMAL,
}
_INT_FIELDS = frozenset({"volume_shares"})

_SID_RE = re.compile(r"[0-9A-Z]{4,12}\Z")
_ROC_RE = re.compile(r"(\d{3})(\d{2})(\d{2})\Z")
_KIND_RE = re.compile(r"[a-z0-9_]{1,32}\Z")
_ZERO = frozenset({"", "-", "--"})


class HarvestError(Exception):
    """取數或解析失敗。訊息刻意不含 URL 以外的環境資訊。"""


_HOST_CTX: dict[str, ssl.SSLContext] = {}      # 主機 → 實際可用的 TLS 設定


def _ssl_candidates() -> list[ssl.SSLContext]:
    """可用的 TLS 設定，依序嘗試。**每一套都是完整驗證**——任何情況都不 `verify=False`。

    為什麼需要兩套：Windows 上實測（2026-07-28）兩個官方主機**各自需要不同的
    CA 來源**，且都以 `Missing Subject Key Identifier` 失敗：

        主機    系統 CA    certifi CA
        TWSE      ✘          ✔
        TPEx      ✔          ✘

    這是憑證鏈**建鏈路徑**的差異，不是憑證不可信（兩者用對的 CA 都 HTTP 200）。
    Linux/GitHub Actions 用系統 CA 兩者皆通，所以 CI 上第一套就會成功；
    certifi 僅為本機（Windows）測試方便，是**選用**相依，本檔仍零必要相依。
    """
    out = []
    for maker in (lambda: ssl.create_default_context(),
                  _certifi_context):
        try:
            ctx = maker()
        except Exception:  # noqa: BLE001 - certifi 沒裝就跳過
            continue
        if ctx is not None:
            ctx.check_hostname = True
            ctx.verify_mode = ssl.CERT_REQUIRED
            out.append(ctx)
    return out


def _certifi_context():
    import certifi  # noqa: PLC0415 - 選用
    return ssl.create_default_context(cafile=certifi.where())


# ---------------------------------------------------------------- 傳輸
def fetch(url: str) -> bytes:
    """只對白名單主機發 HTTPS GET。**不跟隨跨主機重導**，並限制回應大小。

    Linux/macOS 用系統 CA（Actions runner 適用）；不使用 `verify=False`，
    也不接受自帶憑證——降低被中間人替換來源的可能。
    """
    _check_url(url, redirected=False)
    req = urllib.request.Request(
        url, method="GET",
        headers={"Accept": "application/json",
                 "User-Agent": "stock-k-open-data/1.0 (+github-actions)"})
    host = (urlsplit(url).hostname or "").lower()
    known = _HOST_CTX.get(host)
    candidates = [known] if known is not None else _ssl_candidates()
    if not candidates:
        raise HarvestError("找不到可用的 TLS 設定")

    last = None
    for ctx in candidates:
        try:
            with urllib.request.urlopen(req, timeout=TIMEOUT, context=ctx) as resp:  # noqa: S310
                if resp.status != 200:
                    raise HarvestError(f"HTTP {resp.status}: {url}")
                _check_url(resp.geturl(), redirected=True)
                payload = resp.read(MAX_BYTES + 1)
            _HOST_CTX[host] = ctx                 # 記住這台主機用哪套建鏈成功
            if len(payload) > MAX_BYTES:
                raise HarvestError(f"回應超過 {MAX_BYTES} bytes 上限: {url}")
            return payload
        except HTTPError as exc:
            raise HarvestError(f"HTTP {exc.code}: {url}") from exc   # 伺服器有回應，換 CA 無用
        except (HTTPException, URLError, TimeoutError, OSError) as exc:
            last = exc
            continue                              # 可能是建鏈失敗 → 試下一套
    raise HarvestError(f"{type(last).__name__}: {url}") from last


def _check_url(url: str, *, redirected: bool) -> None:
    try:
        loc = urlsplit(url)
        port = loc.port
    except ValueError as exc:
        raise HarvestError("URL 格式無效") from exc
    ok = (loc.scheme == "https" and (loc.hostname or "").lower() in ALLOWED_HOSTS
          and port in (None, 443) and loc.username is None and loc.password is None)
    if not ok:
        raise HarvestError(("重導到白名單外的主機: " if redirected else "非白名單主機: ") + url)


def load_json(raw: bytes, label: str) -> list:
    try:
        doc = json.loads(raw.decode("utf-8-sig"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise HarvestError(f"{label} 不是有效 JSON") from exc
    if not isinstance(doc, list) or not doc:
        raise HarvestError(f"{label} 不是非空陣列")
    return doc


# ---------------------------------------------------------------- 解析
def parse_roc_date(v) -> date:
    """``"1150724"`` → ``2026-07-24``。解析不出來就 raise，**絕不退回今天**。"""
    m = _ROC_RE.match(str(v).strip())
    if not m:
        raise HarvestError(f"民國日期無法解析: {v!r}")
    roc, mm, dd = int(m.group(1)), int(m.group(2)), int(m.group(3))
    if not 1 <= roc <= 200:
        raise HarvestError(f"民國年超出範圍: {v!r}")
    try:
        return date(roc + 1911, mm, dd)
    except ValueError as exc:
        raise HarvestError(f"不是有效日期: {v!r}") from exc


def _one_date(values, label: str) -> date:
    s = {str(v).strip() for v in values if str(v).strip()}
    if not s:
        raise HarvestError(f"{label} 缺日期欄")
    if len(s) > 1:
        raise HarvestError(f"{label} 日期不一致（上游換日中）: {sorted(s)[:4]}")
    return parse_roc_date(s.pop())


def _i(v) -> int | None:
    """整數欄。**官方以空字串表示 0**——當缺值剔除會丟掉大量資料。"""
    s = str(v).replace(",", "").strip()
    if s in _ZERO:
        return 0
    return int(s) if re.fullmatch(r"[+-]?\d+", s) else None


def _dec(v) -> str | None:
    """價格。以**字串**保存（禁浮點存金額）。0 或非數字視為無成交 → None。"""
    s = str(v).replace(",", "").strip()
    if s in _ZERO:
        return None
    if not re.fullmatch(r"[+-]?\d+(\.\d+)?", s):
        return None
    # "0.00" 是官方對零成交的表示，不是價格；放行會在回測產生 -100% 假虧損。
    return None if float(s) <= 0 else s


def parse_twse_margin(raw: bytes, anchor: bytes) -> tuple[date, dict]:
    """上市融資融券。

    ``MI_MARGN`` **沒有日期欄且會落後**（實測 2026-07-27 當天供 07-24）。
    日期取自同站姊妹表 ``STOCK_DAY_ALL`` 的 ``Date``（同發布週期，實測吻合），
    因此是**取得**而非假定 —— 標成「今天」會讓全上市融資券靜默錯標。
    """
    trade_date = _one_date((r.get("Date") for r in load_json(anchor, "STOCK_DAY_ALL")
                            if isinstance(r, dict)), "STOCK_DAY_ALL")
    out: dict[str, list[int]] = {}
    for r in load_json(raw, "MI_MARGN"):
        if not isinstance(r, dict):
            continue
        sid = str(r.get("股票代號", "")).strip().upper()
        if not _SID_RE.match(sid):
            continue
        v = {k: _i(r.get(c)) for k, c in (
            ("mb", "融資買進"), ("ms", "融資賣出"), ("mr", "融資現金償還"),
            ("mp", "融資前日餘額"), ("mt", "融資今日餘額"),
            ("sc", "融券買進"), ("ss", "融券賣出"), ("sr", "融券現券償還"),
            ("sp", "融券前日餘額"), ("st", "融券今日餘額"))}
        if any(x is None for x in v.values()):
            continue
        # 餘額恆等式（實測全市場零違反）。對不上代表該列有問題 → 不供應。
        if v["mp"] + v["mb"] - v["ms"] - v["mr"] != v["mt"]:
            continue
        if v["sp"] + v["ss"] - v["sc"] - v["sr"] != v["st"]:
            continue
        if v["mt"] < 0 or v["st"] < 0:
            continue
        out[sid] = [v["mt"], v["st"]]
    return trade_date, out


def parse_tpex_margin(raw: bytes) -> tuple[date, dict]:
    """上櫃融資融券。此表自帶 ``Date``。``ShortConvering`` 是官方拼字，勿訂正。"""
    rows = load_json(raw, "tpex_margin")
    trade_date = _one_date((r.get("Date") for r in rows if isinstance(r, dict)), "tpex_margin")
    out: dict[str, list[int]] = {}
    for r in rows:
        if not isinstance(r, dict):
            continue
        sid = str(r.get("SecuritiesCompanyCode", "")).strip().upper()
        if not _SID_RE.match(sid):
            continue
        v = {k: _i(r.get(c)) for k, c in (
            ("mb", "MarginPurchase"), ("ms", "MarginSales"), ("mr", "CashRedemption"),
            ("mp", "MarginPurchaseBalancePreviousDay"), ("mt", "MarginPurchaseBalance"),
            ("sc", "ShortConvering"), ("ss", "ShortSale"), ("sr", "StockRedemption"),
            ("sp", "ShortSaleBalancePreviousDay"), ("st", "ShortSaleBalance"))}
        if any(x is None for x in v.values()):
            continue
        if v["mp"] + v["mb"] - v["ms"] - v["mr"] != v["mt"]:
            continue
        if v["sp"] + v["ss"] - v["sc"] - v["sr"] != v["st"]:
            continue
        if v["mt"] < 0 or v["st"] < 0:
            continue
        out[sid] = [v["mt"], v["st"]]
    return trade_date, out


# 官方欄名含多餘空白，是取值關鍵，勿「整理」。
_F_EXCL = ("Foreign Investors include Mainland Area Investors "
           "(Foreign Dealers excluded)-Difference")
_F_DEAL = "ForeignDealers-Difference"
_F_INCL = "ForeignInvestorsInclude MainlandAreaInvestors-Difference"


def parse_tpex_inst(raw: bytes) -> tuple[date, dict]:
    """上櫃三大法人。

    外資取**含外資自營商**那欄（``_F_INCL``），與 FinMind 的
    ``Foreign_Investor + Foreign_Dealer_Self`` 定義一致。實測當日外資自營商
    全為 0、兩欄同值，選錯今天看不出差別，等到有外資自營商成交那天才默默偏離。
    """
    rows = load_json(raw, "tpex_3insti")
    trade_date = _one_date((r.get("Date") for r in rows if isinstance(r, dict)), "tpex_3insti")
    out: dict[str, list[int]] = {}
    for r in rows:
        if not isinstance(r, dict):
            continue
        sid = str(r.get("SecuritiesCompanyCode", "")).strip().upper()
        if not _SID_RE.match(sid):
            continue
        v = {k: _i(r.get(c)) for k, c in (
            ("incl", _F_INCL), ("excl", _F_EXCL), ("fd", _F_DEAL),
            ("tr", "SecuritiesInvestmentTrustCompanies-Difference"),
            ("dl", "Dealers-Difference"), ("tot", "TotalDifference"))}
        if any(x is None for x in v.values()):
            continue
        # 兩道閘門（實測全市場成立）：含＝不含＋外資自營；三類之和＝合計。
        if v["incl"] != v["excl"] + v["fd"]:
            continue
        if v["incl"] + v["tr"] + v["dl"] != v["tot"]:
            continue
        out[sid] = [v["incl"], v["tr"], v["dl"], v["tot"]]
    return trade_date, out


def parse_twse_price(raw: bytes) -> tuple[date, dict]:
    rows = load_json(raw, "STOCK_DAY_ALL")
    trade_date = _one_date((r.get("Date") for r in rows if isinstance(r, dict)), "STOCK_DAY_ALL")
    out: dict[str, list] = {}
    for r in rows:
        if not isinstance(r, dict):
            continue
        sid = str(r.get("Code", "")).strip().upper()
        if not _SID_RE.match(sid):
            continue
        o, h, lo, c = (_dec(r.get(k)) for k in
                       ("OpeningPrice", "HighestPrice", "LowestPrice", "ClosingPrice"))
        vol = _i(r.get("TradeVolume"))
        if None in (o, h, lo, c) or vol is None:
            continue                      # 四價不齊＝當日無有效成交，整筆不供應
        out[sid] = [o, h, lo, c, vol]
    return trade_date, out


def parse_tpex_price(raw: bytes) -> tuple[date, dict]:
    rows = load_json(raw, "tpex_quotes")
    trade_date = _one_date((r.get("Date") for r in rows if isinstance(r, dict)), "tpex_quotes")
    out: dict[str, list] = {}
    for r in rows:
        if not isinstance(r, dict):
            continue
        sid = str(r.get("SecuritiesCompanyCode", "")).strip().upper()
        if not _SID_RE.match(sid):
            continue
        o, h, lo, c = (_dec(r.get(k)) for k in ("Open", "High", "Low", "Close"))
        vol = _i(r.get("TradingShares"))
        if None in (o, h, lo, c) or vol is None:
            continue
        out[sid] = [o, h, lo, c, vol]
    return trade_date, out


# ---------------------------------------------------------------- 落地
def _safe_kind(kind: str) -> str:
    if not _KIND_RE.match(kind or "") or kind not in KIND_FIELDS:
        raise HarvestError(f"未知的 kind: {kind!r}")
    return kind


def save(base: Path, kind: str, trade_date: date, rows: dict, source: str) -> tuple[Path, int]:
    """寫入一天的全市場快照。冪等；內容變動記為修訂並留稽核鏈。

    回傳 ``(路徑, revision)``。原子寫入（先寫暫存再換檔），避免半截 JSON。
    """
    _safe_kind(kind)
    d = Path(base) / DIRNAME / kind
    d.mkdir(parents=True, exist_ok=True)
    f = d / f"{trade_date.isoformat()}.json"
    checksum = hashlib.sha256(
        json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

    revision, previous = 1, None
    if f.exists():
        try:
            old = json.loads(f.read_text(encoding="utf-8"))
        except Exception:  # noqa: BLE001
            old = None
        if isinstance(old, dict):
            if old.get("checksum") == checksum:
                return f, int(old.get("revision") or 1)     # 冪等，不動檔案
            revision = int(old.get("revision") or 1) + 1
            previous = old.get("checksum")

    doc = {
        "schema": SCHEMA_VERSION, "kind": kind, "license": LICENSE_OPEN,
        "trade_date": trade_date.isoformat(), "source": source,
        "fetched_at": datetime.now(timezone.utc).isoformat(),
        "fields": list(KIND_FIELDS[kind]),
        "value_type": KIND_VALUE_TYPE[kind],
        "revision": revision, "checksum": checksum, "previous_checksum": previous,
        "rows": rows,
    }
    tmp = f.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(doc, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
    os.replace(tmp, f)
    return f, revision


def coverage(base: Path) -> dict:
    out = {}
    for kind in KIND_FIELDS:
        d = Path(base) / DIRNAME / kind
        days = sorted(p.stem for p in d.glob("*.json")) if d.is_dir() else []
        out[kind] = {"days": len(days), "first": days[0] if days else None,
                     "last": days[-1] if days else None}
    return out


# ---------------------------------------------------------------- 流程
def run(base: Path) -> int:
    print(f"輸出：{base / DIRNAME}\n")
    failed = 0
    anchor = None
    try:
        anchor = fetch(U_TWSE_PRICE)
    except HarvestError as exc:
        print(f"  [FAIL ] 上市日K/日期錨定  {exc}")
        failed += 1

    jobs = []
    if anchor is not None:
        jobs.append(("price_twse", "上市日 K", lambda: parse_twse_price(anchor),
                     "twse_openapi_stock_day_all"))
        jobs.append(("margin_twse", "上市融資融券",
                     lambda: parse_twse_margin(fetch(U_TWSE_MARGIN), anchor),
                     "twse_openapi_mi_margn"))
    jobs += [
        ("margin_tpex", "上櫃融資融券", lambda: parse_tpex_margin(fetch(U_TPEX_MARGIN)),
         "tpex_openapi_margin_balance"),
        ("inst_tpex", "上櫃三大法人", lambda: parse_tpex_inst(fetch(U_TPEX_INST)),
         "tpex_openapi_3insti_daily"),
        ("price_tpex", "上櫃日 K", lambda: parse_tpex_price(fetch(U_TPEX_PRICE)),
         "tpex_openapi_quotes"),
    ]
    for kind, label, fn, source in jobs:
        try:
            trade_date, rows = fn()
            if not rows:
                raise HarvestError("沒有任何一列通過驗證")
            _, rev = save(base, kind, trade_date, rows, source)
        except HarvestError as exc:
            print(f"  [FAIL ] {label:<12} {exc}")
            failed += 1
            continue
        note = f"（修訂 rev{rev}）" if rev > 1 else ""
        print(f"  [  OK ] {label:<12} {trade_date}　{len(rows):,} 檔{note}")

    print()
    show(base)
    return 1 if failed else 0


def show(base: Path) -> int:
    print(f"累積狀況（{base / DIRNAME}）：")
    for kind, c in coverage(base).items():
        if c["days"]:
            print(f"  {kind:<12} {c['days']:>4} 個交易日　{c['first']} … {c['last']}")
        else:
            print(f"  {kind:<12} {'0':>4} 個交易日")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description="台股籌碼開放資料每日收集（零相依）")
    ap.add_argument("--dir", default="data", help="輸出目錄（預設 ./data）")
    ap.add_argument("--status", action="store_true", help="只顯示累積狀況")
    a = ap.parse_args()
    base = Path(a.dir)
    base.mkdir(parents=True, exist_ok=True)
    return show(base) if a.status else run(base)


if __name__ == "__main__":
    sys.exit(main())
