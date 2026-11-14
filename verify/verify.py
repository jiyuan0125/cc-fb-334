#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
日互动指标双链路核对脚本。

数据:
  realtime/realtime_YYYYMMDD.json  实时链路逐日快照, 文件名的日期是【产出日】,
                                   文件内容是该产出日导出的一批业务日记录
  offline.csv                      离线链路官方口径报表, 一行一个业务日
  change.txt                       一次完播率口径变更的公告

产出:
  metric_diff.csv   列: date,metric,diff_bp,cause
  notes.txt         逐日明细 + 逐日版/全期版两版合计差额 + 舍入说明

核对基准与符号
--------------
change.txt 载明"自 2026-09-11 起, 完播率的统计分母由当日播放次数调整为当日
有效播放次数", 且"本次调整自生效日起在【官方口径报表】中执行"。offline.csv
就是这份官方口径报表, 因此:

    离线 offline.csv   = 核对基准
    实时 realtime/*.json = 被核对象
    diff = 实时值 - 离线基准值        (正: 实时偏高; 负: 实时偏低)

取法亦可由数据印验: 变更日之后离线完播率系统性高于实时, 方向与"分母换成
更小的有效播放次数、率值抬升"一致, 说明离线侧才是已执行新口径的一侧, 实时
侧仍按旧分母(播放次数)出数。notes.txt 会给出具体落差区间。

快照取值与重算覆盖
------------------
文件名的日期是产出日, 同一业务日可能出现在多份快照里 (当日那份 + 次日重算
那份)。取值规则: 同一业务日以【最晚产出的那份】为准, 即覆盖后的终值。
"覆盖前后的值以相邻两份快照存在", 故某业务日出现在两份及以上快照, 或只出现
在非当日的快照里, 即判定该业务日为【重算覆盖】日, 其全部指标行统一归因
"重算覆盖"(覆盖前的残缺值只在 notes 中留档, 不参与对差)。

注意: 覆盖日取覆盖后终值, 因此这些行通常与基准一致(diff=0); 差额为零不代表
"无事项", 而是"实时丢数已由次日重算补齐"。

基点与舍入
----------
1 基点(bp) = 0.01 个百分点 = 1e-4。率类指标:
    diff_bp = (实时完播率 - 离线完播率) / 1e-4
保留 1 位小数, 自第 2 位小数起【直接舍去】(向零截断 ROUND_DOWN, 不四舍五入)。
play/uv 为计数类, diff 列直接写整数绝对差, 不做基点换算。

归因四类 (互斥, 每行恰一类; 优先级自上而下)
--------------------------------------------
    双侧缺失 > 重算覆盖 > 口径变更 > 真差异
  · 双侧缺失: 任一侧缺数(含单侧缺数)即无法对数, 差额记 0, 归入本类;
              这些天不计入完播率全期均值的天数。
  · 重算覆盖: 该业务日存在覆盖前后的相邻两份快照。
  · 口径变更: 完播率, 且业务日在变更日(含)之后——两链路分母口径不同。
  · 真差异: 其余可量化差异(变更日前的率差、全部计数类差异)。
变更日前后分开判: 变更日之前的率差一律走真差异。
完全一致的干净匹配(真差异且差额为 0)不写入 CSV, 保持文件聚焦。

全期合计两版
------------
  计数类 play/uv: 两版都取全期总量差额 (等同于逐日差额之和)。
  完播率·逐日版: 各日基点差额(已截断到 0.1bp)的日均值, 再截断到 0.1bp。
  完播率·全期版: 各日原始率差先求全期日均, 最后一次性换算基点并截断。
均值天数均为完播率两侧均有值的天数, 任一侧缺数的天剔除。

用法:
  python -I verify/verify.py [--realtime-dir DIR] [--offline-csv F]
                             [--change-txt F] [--out-csv F] [--out-notes F]
脚本置于仓根下的 verify/ 子目录, 默认数据与产物路径取上一级(仓根);
若上一级没有 realtime/, 则退回脚本所在目录。
"""

import argparse
import csv
import datetime
import glob
import json
import os
import re
import unicodedata
from decimal import Decimal, ROUND_DOWN

METRICS = ("play", "uv", "finish_rate")
RATE_METRICS = frozenset(("finish_rate",))
UNIT = {"play": "次", "uv": "人", "finish_rate": "bp"}

ONE_BP = Decimal("0.0001")     # 1 基点 = 0.01 百分点 = 1e-4
BP_QUANT = Decimal("0.1")      # 基点保留 1 位小数, 其后直接舍去

CAUSE_CALIBER = "口径变更"
CAUSE_RECOMP = "重算覆盖"
CAUSE_BOTH_MISS = "双侧缺失"
CAUSE_REAL = "真差异"
CAUSE_ORDER = (CAUSE_CALIBER, CAUSE_RECOMP, CAUSE_BOTH_MISS, CAUSE_REAL)

SNAP_RE = re.compile(r"^realtime_(\d{4})(\d{2})(\d{2})\.json$")


# --------------------------------------------------------------------------
# 输入解析
# --------------------------------------------------------------------------
def parse_change_date(change_path):
    """从口径公告中解析生效日, 返回 (生效日 'YYYY-MM-DD', 公告全文)。"""
    with open(change_path, "r", encoding="utf-8") as fh:
        text = fh.read()
    m = re.search(r"自\s*(\d{4}-\d{2}-\d{2})\s*起", text)
    if m is None:
        m = re.search(r"(\d{4}-\d{2}-\d{2})", text)
    if m is None:
        raise ValueError("change.txt 中未识别到口径变更生效日期")
    return m.group(1), text


def _cast(metric, raw):
    """单指标取值: 空/None -> None; 率类 -> Decimal; 计数类 -> int。"""
    if raw is None:
        return None
    if isinstance(raw, str):
        raw = raw.strip()
        if raw == "":
            return None
    if metric in RATE_METRICS:
        return Decimal(str(raw))
    return int(raw)


def load_offline(offline_path):
    """离线官方口径报表 -> {业务日: {metric: 值或 None}}。"""
    table = {}
    with open(offline_path, "r", encoding="utf-8", newline="") as fh:
        for row in csv.DictReader(fh):
            date = (row.get("date") or "").strip()
            if not date:
                continue
            table[date] = {m: _cast(m, row.get(m)) for m in METRICS}
    return table


def load_realtime(realtime_dir):
    """
    读取全部实时快照。

    返回:
      obs      {业务日: 覆盖后终值记录}          —— 对差一律用这份
      history  {业务日: [(产出日, 文件名, 记录)]} —— 按产出日升序, 覆盖前值留档
      coverage 重算覆盖业务日集合
    json 浮点以 Decimal 解析, 全程避开二进制浮点误差。
    """
    history = {}
    paths = sorted(glob.glob(os.path.join(realtime_dir, "realtime_*.json")))
    for path in paths:
        fname = os.path.basename(path)
        m = SNAP_RE.match(fname)
        if not m:
            raise ValueError(f"快照文件名不符合 realtime_YYYYMMDD.json: {fname}")
        prod = "%s-%s-%s" % m.groups()
        with open(path, "r", encoding="utf-8") as fh:
            rows = json.load(fh, parse_float=Decimal) or []
        for row in rows:
            date = (row.get("date") or "").strip()
            if not date:
                continue
            rec = {k: _cast(k, row.get(k)) for k in METRICS}
            history.setdefault(date, []).append((prod, fname, rec))

    obs = {}
    coverage = set()
    for date, items in history.items():
        items.sort(key=lambda t: (t[0], t[1]))
        obs[date] = items[-1][2]                      # 最晚产出那份为准
        if len(items) > 1 or items[-1][0] != date:    # 覆盖前后并存 / 非当日才补出
            coverage.add(date)
    return obs, history, coverage


# --------------------------------------------------------------------------
# 差额与归因
# --------------------------------------------------------------------------
def trunc_bp(value):
    """基点保留 1 位小数, 第 2 位起直接舍去 (向零截断)。"""
    return value.quantize(BP_QUANT, rounding=ROUND_DOWN)


def raw_diff(metric, rt_v, off_v):
    """两侧均有值时的原始差额: 率类为 bp (未截断), 计数类为次数/人数。"""
    if metric in RATE_METRICS:
        return (rt_v - off_v) / ONE_BP
    return rt_v - off_v


def fmt_diff(metric, raw):
    """CSV 展示: 率类截断到 0.1bp 并保留 1 位小数; 计数类整数。"""
    if metric in RATE_METRICS:
        return format(trunc_bp(raw), "f")
    return str(raw)


def classify(date, metric, rt_v, off_v, coverage, change_date):
    """返回 (cause, 展示值, 原始差额或 None)。原始差额 None 表示无法量化。"""
    # 1) 任一侧缺数 -> 无法对数, 差额记 0, 归双侧缺失 (含单侧缺数)
    if rt_v is None or off_v is None:
        return CAUSE_BOTH_MISS, "0", None

    raw = raw_diff(metric, rt_v, off_v)

    # 2) 重算覆盖: 该业务日存在覆盖前后的相邻两份快照
    if date in coverage:
        return CAUSE_RECOMP, fmt_diff(metric, raw), raw

    # 3) 口径变更: 仅率类, 且变更日(含)之后; 变更日之前的率差走真差异
    if metric in RATE_METRICS and date >= change_date:
        return CAUSE_CALIBER, fmt_diff(metric, raw), raw

    # 4) 真差异
    return CAUSE_REAL, fmt_diff(metric, raw), raw


def caliber_evidence(start, end, offline, obs, coverage, change_date):
    """按变更日前后分别汇总完播率差额, 供 notes 用数据说明基准取法的方向。

    以【全部两侧均有值且非覆盖日】的天为可比日, 而不是只看 CSV 中有差异的
    行, 这样"可比日数"才是真实分母。覆盖率(覆盖日取终值, 差按构造为 0)不反映
    口径方向, 故剔除。返回 (变更日前, 变更日后), 各为
    (最小绝对值 bp, 最大绝对值 bp, 天数, 是否全部同号) 或 None。
    """
    def agg(sel):
        if not sel:
            return None
        return (min(abs(v) for v in sel), max(abs(v) for v in sel), len(sel),
                all(v > 0 for v in sel) or all(v < 0 for v in sel))

    pre_vals, post_vals = [], []
    for date in daterange(start, end):
        if date in coverage:
            continue
        rt_rec, off_rec = obs.get(date) or {}, offline.get(date) or {}
        rt_v = rt_rec.get("finish_rate")
        off_v = off_rec.get("finish_rate")
        if rt_v is None or off_v is None:
            continue
        bp = raw_diff("finish_rate", rt_v, off_v)
        (pre_vals if date < change_date else post_vals).append(bp)
    return agg(pre_vals), agg(post_vals)


def daterange(start, end):
    d0 = datetime.date.fromisoformat(start)
    d1 = datetime.date.fromisoformat(end)
    cur = d0
    while cur <= d1:
        yield cur.isoformat()
        cur += datetime.timedelta(days=1)


# --------------------------------------------------------------------------
# 合计
# --------------------------------------------------------------------------
def build_totals(start, end, offline, obs):
    """
    逐日版 / 全期版两版合计。

    样本口径两版一致: 实时取覆盖后终值(obs); 任一侧缺数的指标不参与合计,
    完播率均值天数同步剔除该日。
    """
    count = {m: {"rt": 0, "off": 0, "diff": 0, "days": 0} for m in ("play", "uv")}
    daily_bp = []          # 逐日版: 各日已截断的 bp
    raw_bp_list = []       # 全期版: 各日未截断的原始 bp
    excluded = {m: [] for m in METRICS}

    for date in daterange(start, end):
        off_rec = offline.get(date) or {}
        rt_rec = obs.get(date) or {}
        for metric in METRICS:
            rt_v = rt_rec.get(metric)
            off_v = off_rec.get(metric)
            if rt_v is None or off_v is None:
                excluded[metric].append(date)
                continue
            if metric in RATE_METRICS:
                bp = raw_diff(metric, rt_v, off_v)
                raw_bp_list.append(bp)
                daily_bp.append(trunc_bp(bp))
            else:
                count[metric]["rt"] += rt_v
                count[metric]["off"] += off_v
                count[metric]["diff"] += rt_v - off_v
                count[metric]["days"] += 1

    n = len(raw_bp_list)
    daily_ver = (sum(daily_bp, Decimal(0)) / n).quantize(
        BP_QUANT, rounding=ROUND_DOWN) if n else None
    period_ver = (sum(raw_bp_list, Decimal(0)) / n).quantize(
        BP_QUANT, rounding=ROUND_DOWN) if n else None

    return {
        "count": count,
        "rate_days": n,
        "rate_daily": daily_ver,     # 逐日版: 日 bp 均值
        "rate_period": period_ver,   # 全期版: 原始率差日均, 一次换算
        "excluded": excluded,
    }


# --------------------------------------------------------------------------
# 主流程
# --------------------------------------------------------------------------
def main():
    here = os.path.dirname(os.path.abspath(__file__))
    root = os.path.dirname(here)      # 脚本置于 verify/, 数据在上一级仓根目录
    if not os.path.isdir(os.path.join(root, "realtime")):
        root = here
    ap = argparse.ArgumentParser(description="双链路日互动指标核对")
    ap.add_argument("--realtime-dir", default=os.path.join(root, "realtime"))
    ap.add_argument("--offline-csv", default=os.path.join(root, "offline.csv"))
    ap.add_argument("--change-txt", default=os.path.join(root, "change.txt"))
    ap.add_argument("--out-csv", default=os.path.join(root, "metric_diff.csv"))
    ap.add_argument("--out-notes", default=os.path.join(root, "notes.txt"))
    args = ap.parse_args()

    change_date, _notice = parse_change_date(args.change_txt)
    offline = load_offline(args.offline_csv)
    obs, history, coverage = load_realtime(args.realtime_dir)

    dates = sorted(set(offline) | set(obs) |
                   {p for items in history.values() for p, _, _ in items})
    if not dates:
        raise SystemExit("未读到任何业务日")
    start, end = dates[0], dates[-1]

    rows = []
    for date in daterange(start, end):
        off_rec = offline.get(date) or {}
        rt_rec = obs.get(date) or {}
        for metric in METRICS:
            rt_v = rt_rec.get(metric)
            off_v = off_rec.get(metric)
            cause, shown, raw = classify(
                date, metric, rt_v, off_v, coverage, change_date)
            # 完全一致的干净匹配 (真差异且量化差额恰为 0) 不产出
            if cause == CAUSE_REAL and raw is not None and raw == 0:
                continue
            rows.append({
                "date": date, "metric": metric,
                "diff_bp": shown, "cause": cause,
                "rt": rt_v, "off": off_v, "raw": raw,
            })

    metric_order = {m: i for i, m in enumerate(METRICS)}
    rows.sort(key=lambda r: (r["date"], metric_order[r["metric"]]))

    with open(args.out_csv, "w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["date", "metric", "diff_bp", "cause"])
        w.writeheader()
        for r in rows:
            w.writerow({k: r[k] for k in ("date", "metric", "diff_bp", "cause")})

    totals = build_totals(start, end, offline, obs)
    write_notes(args.out_notes, start, end, change_date, coverage, history,
                rows, totals, offline, obs)
    print(f"已写出 {args.out_csv} ({len(rows)} 行) 与 {args.out_notes}")


# --------------------------------------------------------------------------
# notes.txt
# --------------------------------------------------------------------------
def _signed_int(v):
    return f"+{v}" if v > 0 else str(v)


def _signed_dec(v):
    s = format(v, "f")
    return "+" + s if v > 0 else s


def _w(text):
    """终端显示宽度: 东亚宽字符按 2 列计。"""
    return sum(2 if unicodedata.east_asian_width(ch) in ("W", "F") else 1
               for ch in text)


def _pad(text, width, align="left"):
    """按显示宽度补空格, 避免 CJK 列错位。"""
    text = str(text)
    gap = max(width - _w(text), 0)
    if align == "right":
        return " " * gap + text
    return text + " " * gap


def write_notes(path, start, end, change_date, coverage, history, rows, totals,
                offline, obs):
    ndays = len(list(daterange(start, end)))
    cause_count = {c: 0 for c in CAUSE_ORDER}
    for r in rows:
        cause_count[r["cause"]] += 1

    L = []
    p = L.append
    p("日互动指标双链路核对说明")
    p("=" * 68)
    p(f"核对区间: {start} 至 {end}, 共 {ndays} 个自然日")
    p(f"口径变更生效日: {change_date} (change.txt)")
    p("")

    p("一、核对基准与差额符号")
    p("-" * 68)
    p("change.txt 说明: 自 " + change_date + " 起, 完播率的统计分母由当日播放次数")
    p("调整为当日有效播放次数, 且本次调整在【官方口径报表】中执行、此前历史不追")
    p("溯。offline.csv 即这份官方口径报表, 故取【离线为核对基准, 实时为被核对")
    p("象】, 差额符号统一为:")
    p("        diff = 实时值 - 离线基准值")
    p("  · 正数: 实时偏高; 负数: 实时偏低。")
    p("  · play/uv 为计数绝对差(次 / 人), 不做基点换算;")
    p("  · finish_rate 换算为基点: 1 bp = 0.01 个百分点 = 1e-4,")
    p("        diff_bp = (实时完播率 - 离线完播率) / 1e-4")
    pre, post = caliber_evidence(start, end, offline, obs, coverage, change_date)
    if post:
        lo, hi, n, same_sign = post
        p("  数据本身印证该取法: 变更日(含)之后 %d 个可比日里, 实时完播率%s离线" %
          (n, "全部低于" if same_sign else "与离线差异(符号不一致, 见 CSV)"))
        p("基准, 落差 %.1f~%.1f bp(约 %.1f~%.1f 个百分点), 方向与'分母换成更小的有效"
          % (lo, hi, lo / 100, hi / 100))
        p("播放次数、率值抬升'一致, 说明新口径已在离线官方报表落地;")
        if pre:
            p("变更日之前 %d 个可比日的率差绝对值不超过 %.1f bp, 属同口径下的数据差。" %
              (pre[2], pre[1]))
        else:
            p("变更日之前无率类分母可比项。")
    p("")
    p("  变更日前后分开判: 口径变更归因只对 finish_rate 且仅对变更日(含)之后的")
    p("  行生效; 变更日之前的率差一律按真差异处理。")
    p("")

    p("二、快照取值与重算覆盖")
    p("-" * 68)
    p("快照文件名中的日期是【产出日】。同一业务日出现在多份快照时, 以最晚产出那")
    p("份为准(即覆盖后的终值); 覆盖前后的两个值由相邻两份快照留档, 覆盖前的残")
    p("缺值只在本节留档, 不参与对差。判定为覆盖日的业务日, 其全部指标行归因")
    p("\"重算覆盖\"。")
    if coverage:
        p(f"  本样例覆盖日: {', '.join(sorted(coverage))} (共 {len(coverage)} 天)")
        p("")
        p("  覆盖前后留档 (缺数 -> 次日重算):")
        p("    " + _pad("业务日", 12) + _pad("指标", 14) + _pad("覆盖前", 12, "right")
          + _pad("覆盖后(采用)", 16, "right") + _pad("补回", 10, "right"))
        for date in sorted(coverage):
            items = history[date]
            pre = items[0][2]
            post = items[-1][2]
            for metric in METRICS:
                a, b = pre.get(metric), post.get(metric)
                av = "缺" if a is None else format(a, "f") if metric in RATE_METRICS else str(a)
                bv = "缺" if b is None else format(b, "f") if metric in RATE_METRICS else str(b)
                if a is None or b is None:
                    delta = "-"
                elif metric in RATE_METRICS:
                    delta = _signed_dec(trunc_bp(raw_diff(metric, b, a)))
                else:
                    delta = _signed_int(b - a)
                p("    " + _pad(date, 12) + _pad(metric, 14)
                  + _pad(av, 12, "right") + _pad(bv, 16, "right")
                  + _pad(delta, 10, "right"))
        p("")
        p("  覆盖日取覆盖后终值对差, 故这些行的 diff 通常为 0——零差额的含义是")
        p("  \"实时丢数已由次日重算补齐\", 不是\"无事项\"; CSV 仍逐行产出并标注")
        p("  \"重算覆盖\", 以免被误读为干净匹配。")
    else:
        p("  本样例无覆盖日。")
    p("")

    p("三、基点舍入规则")
    p("-" * 68)
    p("  基点值保留 1 位小数, 自第 2 位小数起直接舍去(向零截断 ROUND_DOWN, 不")
    p("  四舍五入): 4.55 bp -> 4.5 bp; -410.88 bp -> -410.8 bp; -240.01 bp ->")
    p("  -240.0 bp。play/uv 为整数差, 无舍入。任一侧缺数的行无法对数, diff_bp")
    p("  记 0 (计数类写 0, 率类同样写 0 而非 0.0, 以示为占位而非量算值)。")
    p("")

    p("四、四类归因 (互斥, 每行恰一类; 优先级自上而下)")
    p("-" * 68)
    p("  双侧缺失 > 重算覆盖 > 口径变更 > 真差异")
    p("  · 双侧缺失: 任一侧缺数(含仅单侧缺数)即无法对数, 差额记 0, 归入本类;")
    p("              这些天不计入完播率全期均值的天数。")
    p("  · 重算覆盖: 该业务日存在覆盖前后的相邻两份快照。")
    p("  · 口径变更: finish_rate 且业务日在变更日(含)之后, 两侧分母口径不同。")
    p("  · 真差异: 其余可量化差异(变更日前的率差、全部计数类差异)。")
    p("  完全一致的干净匹配(真差异且差额为 0)不写入 CSV, 以保持文件聚焦。")
    p("")

    p("五、逐日差额明细")
    p("-" * 68)
    p("  单位: play/uv 为次/人, finish_rate 为基点(bp); 仅列有差异、缺失或覆盖的行。")
    p("")
    p("  " + _pad("date", 12) + _pad("metric", 14) + _pad("diff_bp", 10, "right")
      + "  " + _pad("cause", 10) + _pad("实时", 12, "right")
      + _pad("离线", 12, "right"))
    for r in rows:
        rt_s = "-" if r["rt"] is None else (
            format(r["rt"], "f") if r["metric"] in RATE_METRICS else str(r["rt"]))
        off_s = "-" if r["off"] is None else (
            format(r["off"], "f") if r["metric"] in RATE_METRICS else str(r["off"]))
        p("  " + _pad(r["date"], 12) + _pad(r["metric"], 14)
          + _pad(r["diff_bp"], 10, "right") + "  " + _pad(r["cause"], 10)
          + _pad(rt_s, 12, "right") + _pad(off_s, 12, "right"))
    p("")

    p("六、全期合计差额 (逐日版 / 全期版)")
    p("-" * 68)
    p("  两版样本口径一致: 实时取覆盖后终值; 任一侧缺数的指标不参与合计;")
    p(f"  完播率参与均值天数 = {totals['rate_days']} 天 (剔除任一侧缺数的天)。")
    p("  数值指标(play/uv)两版一致, 均取【全期总量差额】(逐日差额之和, 等同两")
    p("  侧全期总量之差), 为整数, 不舍入。")
    p("")
    p("  指标          逐日版                      全期版")
    for metric in ("play", "uv"):
        c = totals["count"][metric]
        cell = f"{_signed_int(c['diff'])} {UNIT[metric]} (全期总量)"
        p("  " + _pad(metric, 14) + _pad(cell, 28)
          + f"{_signed_int(c['diff'])} {UNIT[metric]} (全期总量)")
    rd = ("-" if totals["rate_daily"] is None
          else f"{_signed_dec(totals['rate_daily'])} bp (日均)")
    rp = ("-" if totals["rate_period"] is None
          else f"{_signed_dec(totals['rate_period'])} bp (日均)")
    p("  " + _pad("finish_rate", 14) + _pad(rd, 28) + rp)
    p("")
    for metric in ("play", "uv"):
        c = totals["count"][metric]
        excl = totals["excluded"][metric]
        p(f"  {metric}: 实时合计 {c['rt']} {UNIT[metric]} - 离线合计 {c['off']} "
          f"{UNIT[metric]} = 差 {_signed_int(c['diff'])} {UNIT[metric]}"
          f" (参与 {c['days']} 天" + (f"; 剔除 {', '.join(excl)})" if excl else ")"))
    p("")
    p("  【完播率 · 逐日版】先逐日换算并截断, 再对日 bp 求平均")
    p("    舍入: 每日率差先换算基点、截断到 0.1 bp(第 2 位起舍去), 再对")
    p(f"          {totals['rate_days']} 个日 bp 取算术平均, 均值同样截断到 0.1 bp。")
    p("    结果: " + ("-" if totals["rate_daily"] is None
                   else f"{_signed_dec(totals['rate_daily'])} bp (日均)"))
    p("")
    p("  【完播率 · 全期版】先求全期日均原始差额, 最后一次换算基点")
    p("    舍入: 用未截断的各日原始率差求日均, 仅在换算成基点后截断一次(到")
    p("          0.1 bp), 全程只舍一次, 不累积逐日截断误差。")
    p("    结果: " + ("-" if totals["rate_period"] is None
                   else f"{_signed_dec(totals['rate_period'])} bp (日均)"))
    p("")
    if totals["rate_daily"] is not None and totals["rate_period"] is not None:
        gap = totals["rate_daily"] - totals["rate_period"]
        p(f"    两版之差 = {_signed_dec(gap)} bp, 全部来自逐日版的逐日截断累积;")
        p("    全期版只舍一次, 更贴近真实净差额。")
    p("")
    miss_rows = []
    for metric in METRICS:
        for date in totals["excluded"][metric]:
            miss_rows.append((date, metric))
    if miss_rows:
        p("  因任一侧缺数而未纳入合计的项 (diff 记 0, 且不计入完播率均值天数):")
        for date, metric in sorted(miss_rows):
            p(f"    {date}  {metric}")
        p("")

    p("七、产出统计")
    p("-" * 68)
    p(f"  metric_diff.csv 数据行数(不含表头): {len(rows)}")
    for cause in CAUSE_ORDER:
        p(f"    {cause}: {cause_count[cause]} 行")
    p("  完全一致的干净匹配行不写入 CSV。")

    with open(path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(L) + "\n")


if __name__ == "__main__":
    main()
