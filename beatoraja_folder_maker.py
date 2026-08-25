#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
beatoraja カスタムフォルダ作成ツール
====================================

難易度表・BPM・BP の条件を1画面で選び、掛け合わせたフォルダを
beatoraja の folder/default.json に生成・追記するGUIツールです。
生成済みのフォルダを一覧して個別に削除することもできます。

仕様の根拠（beatoraja 本体ソース）
  - 読み込まれるのは folder/default.json のみ（ハードコード）
      BarManager.java: Paths.get("folder/default.json")
  - JSONで使えるキーは name / sql / folder / showall / rcourse の5つのみ。
    未知のキーが1つでもあるとカスタムフォルダ全体が読み込まれません。
  - "sql" の値は WHERE 句の中身として連結されます。
      SQLiteSongDatabaseAccessor#getSongDatas():
        SELECT DISTINCT ... FROM (song LEFT JOIN reviewdb.review) AS song
        LEFT OUTER JOIN (score LEFT OUTER JOIN scorelog ON ...) ON ... WHERE <sql>
  - 参照できるのは song.* / score.* / scorelog.* / information.*（songinfo.db有効時）
  - 難易度表のレベルは songdata.db に入らないため（table/*.bmt に保存される）、
    SQLから直接は絞り込めません。本ツールは難易度表の配布JSONから md5 を取得し、
    song.md5 IN (...) という形のSQLに展開することで同等のフォルダを作ります。

標準ライブラリのみで動作します（Python 3.9+ / tkinter）。
"""

from __future__ import annotations

import itertools
import json
import os
import queue
import re
import shutil
import sqlite3
import sys
import threading
import time
import traceback
import urllib.error
import urllib.request
from datetime import datetime
from pathlib import Path
from urllib.parse import urljoin

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

APP_TITLE = "beatoraja カスタムフォルダ作成ツール"
USER_AGENT = "beatoraja-folder-maker/1.1 (+python-urllib)"
FALLBACK_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
               "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")
HTTP_TIMEOUT = 60

# ---------------------------------------------------------------------------
# 難易度表（既定）
#   URLは header.json を直接指定。HTMLページのURLを入れた場合は
#   <meta name="bmstable"> から header を自動解決します。
# ---------------------------------------------------------------------------
BUILTIN_TABLES = [
    ("Satellite", "https://stellabms.xyz/sl/header.json"),
    ("Stella", "https://stellabms.xyz/st/header.json"),
    ("発狂BMS難易度表（★・GENOCIDE）",
     "https://miraiscarlet.github.io/bms/table/genocide_insane/header_insane.json"),
    ("NEW GENERATION 発狂難易度表（▼・第二期）",
     "https://rattoto10.github.io/second_table/insane_header.json"),
    ("第2通常難易度表（▽）", "https://bmsnormal2.syuriken.jp/js/header.json"),
]

# 名前に使う記号。スキンのフォントで表示できない場合はここだけ変えれば全体に効く。
#   RANGE_DASH … BPM や DJ LEVEL の範囲を表すつなぎ
#   LE_SYMBOL  … BP の「以下」を表す記号。表示できない環境では "<=" にする
RANGE_DASH = " - "
LE_SYMBOL = "≦"


def bpm_name(lo, hi, changed: bool = False) -> str:
    """BPMの区切りの名前を自動で作る。"""
    if changed:
        return "BPM変化あり"
    if lo is not None and hi is not None:
        return f"{lo}{RANGE_DASH}{hi}" if lo != hi else f"BPM{lo}"
    if hi is not None:
        return f"{RANGE_DASH.lstrip()}{hi}"
    if lo is not None:
        return f"{lo}{RANGE_DASH.rstrip()}"
    return "BPM"


def bp_name(lo, hi) -> str:
    """BPの区切りの名前を自動で作る。"""
    if lo is not None and hi is not None:
        if lo == hi:
            return f"BP{lo}"
        return f"{lo}{LE_SYMBOL}BP{LE_SYMBOL}{hi}"
    if hi is not None:
        return f"BP{LE_SYMBOL}{hi}"
    if lo is not None:
        return f"{lo}{LE_SYMBOL}BP"
    return "BP"


DEFAULT_BPM_RANGES = [
    (f"低速{RANGE_DASH}100", None, 100, False),
    (f"中速 101{RANGE_DASH}160", 101, 160, False),
    (f"高速 161{RANGE_DASH}300", 161, 300, False),
    (f"光速 301{RANGE_DASH.rstrip()}", 301, None, False),
    ("ソフラン", None, None, True),
]

DEFAULT_BP_RANGES = [
    (bp_name(None, 10), None, 10),
    (bp_name(11, 20), 11, 20),
    (bp_name(21, 30), 21, 30),
    (bp_name(31, 50), 31, 50),
    (bp_name(51, None), 51, None),
]

# クリアランプ。値は beatoraja の ClearType の id。
#   ClearType.java: NoPlay(0), Failed(1), AssistEasy(2), LightAssistEasy(3),
#                   Easy(4), Normal(5), Hard(6), ExHard(7), FullCombo(8),
#                   Perfect(9), Max(10)
CLEAR_LAMPS = [
    ("NO PLAY", 0), ("FAILED", 1), ("ASSIST", 2), ("L-ASSIST", 3),
    ("EASY", 4), ("CLEAR", 5), ("HARD", 6), ("EX-HARD", 7),
    ("FULLCOMBO", 8), ("PERFECT", 9), ("MAX", 10),
]
LAMP_NAMES = [name for name, _id in CLEAR_LAMPS]
LAMP_IDS = dict(CLEAR_LAMPS)

DEFAULT_LAMP_RANGES = [
    ("FAILED", "FAILED", "FAILED"),
    ("ASSIST", "ASSIST", "L-ASSIST"),
    ("EASY", "EASY", "EASY"),
    ("CLEAR", "CLEAR", "CLEAR"),
    ("HARD", "HARD", "HARD"),
    ("EX-HARD", "EX-HARD", "EX-HARD"),
    ("FULLCOMBO", "FULLCOMBO", "FULLCOMBO"),
]

# DJ LEVEL。値はスコアレートのしきい値（9分のいくつ以上か）。
#   スコアレート = EXスコア / (ノート数 * 2)
#   AAA=8/9, AA=7/9, A=6/9, B=5/9, C=4/9, D=3/9, E=2/9, それ未満がF
DJ_LEVELS = ["F", "E", "D", "C", "B", "A", "AA", "AAA"]
DJ_LEVEL_NINTHS = {"F": 0, "E": 2, "D": 3, "C": 4,
                   "B": 5, "A": 6, "AA": 7, "AAA": 8}

DEFAULT_SCORE_RANGES = [
    (f"DJ LEVEL{RANGE_DASH}B", "F", "B"),
    ("DJ LEVEL A", "A", "A"),
    ("DJ LEVEL AA", "AA", "AA"),
    ("DJ LEVEL AAA", "AAA", "AAA"),
]

# EXスコア。PGREAT2点 + GREAT1点。
EX_SCORE = "((score.epg + score.lpg) * 2 + score.egr + score.lgr)"

MD5_RE = re.compile(r"^[0-9a-f]{32}$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
META_RE = re.compile(r"<meta[^>]*name\s*=\s*[\"']bmstable[\"'][^>]*>", re.IGNORECASE)
META_ALT_RE = re.compile(r"<meta[^>]*name\s*=\s*[\"']bmstable-alt[\"'][^>]*>", re.IGNORECASE)
CONTENT_RE = re.compile(r"content\s*=\s*[\"']([^\"']+)[\"']", re.IGNORECASE)

# IN句を分割する単位。SQLite の式ツリー深度制限に余裕を持たせる目的。
IN_CHUNK = 400

# この大きさを超えたら確認する（バイト）
SIZE_WARN = 3 * 1024 * 1024

ALLOWED_KEYS = {"name", "sql", "folder", "showall", "rcourse"}

# 生成したフォルダを入れる、一番上の階層のフォルダ名
ROOT_NAME = "カスタムフォルダ"


# ===========================================================================
# 通信・難易度表の読み込み
# ===========================================================================
def http_get(url: str, timeout: int = HTTP_TIMEOUT) -> bytes:
    """URLからバイト列を取得する。UAを弾くサーバー向けに一度だけ再試行する。"""
    last = None
    for ua in (USER_AGENT, FALLBACK_UA):
        req = urllib.request.Request(url, headers={"User-Agent": ua, "Accept": "*/*"})
        try:
            with urllib.request.urlopen(req, timeout=timeout) as res:
                return res.read()
        except urllib.error.HTTPError as e:
            last = e
            if e.code not in (403, 406, 429):
                raise
        except urllib.error.URLError as e:
            raise ValueError(f"通信できませんでした（{url}）: {e.reason}") from e
    raise ValueError(f"取得に失敗しました（HTTP {last.code}）: {url}")


def decode_text(raw: bytes) -> str:
    """HTML/JSONのバイト列を文字列にする。Shift_JISのページも扱う。"""
    for enc in ("utf-8-sig", "utf-8", "cp932", "euc_jp"):
        try:
            return raw.decode(enc)
        except UnicodeDecodeError:
            continue
    return raw.decode("utf-8", errors="replace")


def resolve_header_url(url: str, fetch=http_get) -> str:
    """URLから header.json のURLを決める。HTMLなら meta name="bmstable" を読む。"""
    url = url.strip()
    if url.lower().split("?")[0].endswith(".json"):
        return url
    html = decode_text(fetch(url))
    for pattern in (META_RE, META_ALT_RE):
        m = pattern.search(html)
        if m:
            c = CONTENT_RE.search(m.group(0))
            if c:
                return urljoin(url, c.group(1).strip())
    raise ValueError("このページから難易度表のヘッダ（meta name=\"bmstable\"）が"
                     "見つかりません: " + url)


def _as_str_list(value) -> list:
    if value is None:
        return []
    if isinstance(value, str):
        return [value]
    if isinstance(value, list):
        return [str(v) for v in value]
    return [str(value)]


def load_table(url: str, fetch=http_get) -> dict:
    """難易度表を取得して {name, symbol, tag, levels:[...]} に整える。"""
    header_url = resolve_header_url(url, fetch=fetch)
    header = json.loads(decode_text(fetch(header_url)))

    name = str(header.get("name") or "").strip() or header_url
    symbol = str(header.get("symbol") or "").strip()
    tag = str(header.get("tag") or "").strip() or symbol
    level_order = [str(v) for v in (header.get("level_order") or [])]

    data_urls = _as_str_list(header.get("data_url"))
    if not data_urls:
        raise ValueError("header.json に data_url がありません: " + header_url)

    records = []
    for du in data_urls:
        parsed = json.loads(decode_text(fetch(urljoin(header_url, du))))
        if isinstance(parsed, dict):
            parsed = parsed.get("data") or []
        records.extend(parsed)

    buckets: dict = {}
    order_seen: list = []
    for rec in records:
        if not isinstance(rec, dict):
            continue
        level = rec.get("level")
        if level is None:
            continue
        level = str(level)
        if level not in buckets:
            buckets[level] = {"md5": [], "sha256": [], "count": 0}
            order_seen.append(level)
        b = buckets[level]
        b["count"] += 1
        md5 = str(rec.get("md5") or "").strip().lower()
        sha = str(rec.get("sha256") or "").strip().lower()
        if MD5_RE.match(md5):
            b["md5"].append(md5)
        elif SHA256_RE.match(sha):
            b["sha256"].append(sha)

    ordered = [lv for lv in level_order if lv in buckets]
    ordered += [lv for lv in order_seen if lv not in ordered]

    levels = []
    for lv in ordered:
        b = buckets[lv]
        levels.append({
            "level": lv,
            "label": f"{tag}{lv}" if tag else lv,
            "md5": sorted(set(b["md5"])),
            "sha256": sorted(set(b["sha256"])),
            "count": b["count"],
        })

    return {"name": name, "symbol": symbol, "tag": tag,
            "header_url": header_url, "levels": levels}


# ===========================================================================
# SQL生成
# ===========================================================================
def _in_clause(column: str, values: list) -> str:
    chunks = []
    for i in range(0, len(values), IN_CHUNK):
        part = ",".join("'" + v + "'" for v in values[i:i + IN_CHUNK])
        chunks.append(f"{column} IN ({part})")
    if len(chunks) == 1:
        return chunks[0]
    return "(" + " OR ".join(chunks) + ")"


def hash_sql(md5s: list, sha256s: list) -> str:
    """md5/sha256 のリストからWHERE句を作る。"""
    parts = []
    if md5s:
        parts.append(_in_clause("song.md5", md5s))
    if sha256s:
        parts.append(_in_clause("song.sha256", sha256s))
    if not parts:
        return ""
    if len(parts) == 1:
        return "(" + parts[0] + ")"
    return "(" + " OR ".join(parts) + ")"


def unpack_range(item) -> tuple:
    """(名前, 下限, 上限) と (名前, 下限, 上限, フラグ) の両方を受ける。"""
    name, lo, hi = item[0], item[1], item[2]
    flag = bool(item[3]) if len(item) > 3 else False
    return name, lo, hi, flag


def bpm_sql(lo, hi, changed: bool = False) -> str:
    """
    BPM条件。song.minbpm / song.maxbpm を使う。
    changed が真なら下限・上限を無視して、BPMが変化する譜面だけにする。
    """
    if changed:
        return "song.minbpm != song.maxbpm"
    conds = []
    if lo is not None:
        conds.append(f"song.minbpm >= {int(lo)}")
    if hi is not None:
        conds.append(f"song.maxbpm <= {int(hi)}")
    if not conds:
        return "1 = 1"
    return " AND ".join(conds)


def bp_sql(lo, hi) -> str:
    """BP条件。score.minbp を使う。未プレイ譜面は minbp が NULL なので除外される。"""
    conds = ["score.minbp IS NOT NULL"]
    if lo is not None:
        conds.append(f"score.minbp >= {int(lo)}")
    if hi is not None:
        conds.append(f"score.minbp <= {int(hi)}")
    return " AND ".join(conds)


def lamp_sql(lo: str, hi: str) -> str:
    """
    クリアランプの範囲（lo以上 hi以下）を表すWHERE句。
    未プレイの譜面は score.clear が NULL のため、どの範囲にも入らない。
    """
    lo_id, hi_id = LAMP_IDS.get(lo), LAMP_IDS.get(hi)
    if lo_id is not None and hi_id is not None and lo_id == hi_id:
        return f"score.clear = {lo_id}"
    conds = []
    if lo_id is not None:
        conds.append(f"score.clear >= {lo_id}")
    if hi_id is not None:
        conds.append(f"score.clear <= {hi_id}")
    return " AND ".join(conds) if conds else "score.clear IS NOT NULL"


def dj_level_sql(lo: str, hi: str) -> str:
    """
    DJ LEVEL の範囲（lo以上 hi以下）を表すWHERE句。
    割り算を使わず整数の掛け算で比べるため、端の1点でずれない。
        スコアレート >= k/9  ⇔  EXスコア * 9 >= ノート数 * 2k
    """
    conds = ["score.notes > 0"]
    k_lo = DJ_LEVEL_NINTHS.get(lo, 0)
    if k_lo > 0:
        conds.append(f"{EX_SCORE} * 9 >= score.notes * {2 * k_lo}")
    if hi in DJ_LEVELS:
        i = DJ_LEVELS.index(hi)
        if i + 1 < len(DJ_LEVELS):
            k_next = DJ_LEVEL_NINTHS[DJ_LEVELS[i + 1]]
            conds.append(f"{EX_SCORE} * 9 < score.notes * {2 * k_next}")
    return " AND ".join(conds)


def and_sql(*parts) -> str:
    """条件をANDで連結する。空文字は無視する。"""
    kept = [p for p in parts if p]
    if not kept:
        return "1 = 1"
    return " AND ".join(kept)


# ===========================================================================
# フォルダ構造の組み立て
#   選ばれた条件を 難易度表 → BPM → BP の順に入れ子にする。
#   選ばれなかった段は飛ばす。
# ===========================================================================
def used_labels(use_bpm: bool, use_bp: bool, use_lamp: bool = False,
                use_score: bool = False) -> list:
    labels = []
    if use_bpm:
        labels.append("BPM")
    if use_bp:
        labels.append("BP")
    if use_lamp:
        labels.append("LAMP")
    if use_score:
        labels.append("SCORE")
    return labels


def suffix_for(use_bpm: bool, use_bp: bool, use_lamp: bool = False,
               use_score: bool = False) -> str:
    labels = used_labels(use_bpm, use_bp, use_lamp, use_score)
    return f"（{'・'.join(labels)}別）" if labels else ""


def auto_title(table_names, use_bpm: bool, use_bp: bool,
               use_lamp: bool = False, use_score: bool = False) -> str:
    """タイトル未入力のときに使う名前を決める。"""
    if table_names:
        return "・".join(table_names) + suffix_for(
            use_bpm, use_bp, use_lamp, use_score)
    labels = used_labels(use_bpm, use_bp, use_lamp, use_score)
    return "・".join(labels) + "別" if labels else ""


def _bp_items(bp_ranges, bp_noplay) -> list:
    items = []
    for item in bp_ranges:
        nm, lo, hi, _flag = unpack_range(item)
        items.append((nm, bp_sql(lo, hi), ""))
    if bp_noplay:
        items.append(("未プレイ", "score.clear IS NULL", "noplay"))
    return items


def _bpm_items(bpm_ranges) -> list:
    items = []
    for item in bpm_ranges:
        nm, lo, hi, changed = unpack_range(item)
        items.append((nm, bpm_sql(lo, hi, changed), ""))
    return items


def _lamp_items(lamp_ranges) -> list:
    return [(item[0], lamp_sql(item[1], item[2]), "score")
            for item in lamp_ranges]


def _score_items(score_ranges) -> list:
    return [(item[0], dj_level_sql(item[1], item[2]), "score")
            for item in score_ranges]


def level_items(tables) -> list:
    """
    選んだ表のレベルを (表示名, WHERE句) の並びにする。
    表示名は記号だけ（sl0、★1）。他の表と重なる場合だけ表名を頭に付ける。
    """
    seen = {}
    for table in tables:
        for lv in table["levels"]:
            seen[lv["label"]] = seen.get(lv["label"], 0) + 1

    items = []
    for table in tables:
        for lv in table["levels"]:
            cond = hash_sql(lv["md5"], lv["sha256"])
            if not cond:
                continue
            label = lv["label"]
            if seen.get(label, 0) > 1:
                label = f"{table['name']} {label}"
            items.append((label, cond))
    return items


def table_base_sql(tables) -> str:
    """選んだ難易度表に入っている譜面すべて（レベル問わず）を表すWHERE句。"""
    md5s, shas = [], []
    for table in tables:
        for lv in table["levels"]:
            md5s.extend(lv["md5"])
            shas.extend(lv["sha256"])
    return hash_sql(sorted(set(md5s)), sorted(set(shas)))


def build_folder(tables, bpm_conf, bp_conf, lamp_conf=(False, ()),
                 score_conf=(False, ()), title: str = "",
                 split_levels: bool = False) -> list:
    """
    選んだ条件から、入れ子のないフォルダを1つ作って返す。

    難易度表は「その表に入っている譜面だけに絞る」条件として働き、レベルでは
    分けない。中身は BPM → BP → LAMP → SCORE の区切りを掛け合わせたものになる。
    難易度表だけを選んだ場合は、中身がレベルごとのフォルダになる。

    tables:     [ load_table() の結果, ... ]（空なら難易度表なし）
    bpm_conf:   (使う?, [(名前, 下限, 上限, 変化あり?), ...])
    bp_conf:    (使う?, [(名前, 下限, 上限), ...], 未プレイを作る?)
    lamp_conf:  (使う?, [(名前, 下限ランプ, 上限ランプ), ...])
    score_conf: (使う?, [(名前, 下限DJ LEVEL, 上限DJ LEVEL), ...])
    title:      フォルダ名。空なら auto_title() の値を使う
    戻り値:     カスタムフォルダの中に足すフォルダ定義のリスト（0件か1件）
    """
    use_bpm, bpm_ranges = bpm_conf
    use_bp, bp_ranges, bp_noplay = bp_conf
    use_lamp, lamp_ranges = lamp_conf
    use_score, score_ranges = score_conf
    use_bpm = bool(use_bpm and bpm_ranges)
    use_bp = bool(use_bp and (bp_ranges or bp_noplay))
    use_lamp = bool(use_lamp and lamp_ranges)
    use_score = bool(use_score and score_ranges)

    split_levels = bool(split_levels and tables)
    levels = level_items(tables) if split_levels else []
    if split_levels and not levels:
        return []

    base = ""
    if tables and not split_levels:
        base = table_base_sql(tables)
        if not base:
            return []

    dims = []
    if use_bpm:
        dims.append(_bpm_items(bpm_ranges))
    if use_bp:
        dims.append(_bp_items(bp_ranges, bp_noplay))
    if use_lamp:
        dims.append(_lamp_items(lamp_ranges))
    if use_score:
        dims.append(_score_items(score_ranges))

    children = []
    if dims:
        for combo in itertools.product(*dims):
            kinds = {part[2] for part in combo if len(part) > 2}
            # 未プレイ × クリアランプ / DJ LEVEL は必ず空になるので作らない
            if "noplay" in kinds and "score" in kinds:
                continue
            name = " / ".join(part[0] for part in combo)
            cond = and_sql(base, *[part[1] for part in combo])
            if split_levels:
                # 組み合わせのフォルダの中に、レベルごとのフォルダを作る
                children.append({
                    "name": name,
                    "folder": [{"name": lab, "sql": and_sql(cond, lv)}
                               for lab, lv in levels],
                })
            else:
                children.append({"name": name, "sql": cond})
    elif split_levels:
        children = [{"name": lab, "sql": lv} for lab, lv in levels]
    elif tables:
        # 難易度表だけを選んだときは、レベルごとのフォルダにする
        multi = len(tables) > 1
        for table in tables:
            for lv in table["levels"]:
                cond = hash_sql(lv["md5"], lv["sha256"])
                if not cond:
                    continue
                label = f"{table['name']} {lv['label']}" if multi else lv["label"]
                children.append({"name": label, "sql": cond})

    if not children:
        return []

    name = (title or "").strip() or auto_title(
        [t["name"] for t in tables], use_bpm, use_bp, use_lamp, use_score)
    if not name:
        name = "新しいフォルダ"
    return [{"name": name, "folder": children}]


def count_leaves(folders: list) -> int:
    n = 0
    for f in folders:
        if isinstance(f, dict) and f.get("folder"):
            n += count_leaves(f["folder"])
        else:
            n += 1
    return n


def validate_folders(folders: list) -> list:
    """未知のキーが混ざっていないか検査する。問題があれば説明文のリストを返す。"""
    problems = []

    def walk(node, path):
        if not isinstance(node, dict):
            problems.append(f"{path}: オブジェクトではありません")
            return
        for k in node:
            if k not in ALLOWED_KEYS:
                problems.append(
                    f"{path}: 使えないキー \"{k}\" があります"
                    "（name / sql / folder / showall / rcourse のみ有効）")
        if not isinstance(node.get("name"), str) or not node["name"]:
            problems.append(f"{path}: name が空です")
        if "folder" in node:
            for i, child in enumerate(node["folder"] or []):
                walk(child, f"{path}/{node.get('name', '?')}[{i}]")

    for i, f in enumerate(folders):
        walk(f, f"[{i}]")
    return problems


# ===========================================================================
# ファイルの読み書き
# ===========================================================================
def read_existing(path: Path):
    """既存の default.json を読む。戻り値 (folders, error_message)。"""
    if not path.exists():
        return [], None
    try:
        text = path.read_text(encoding="utf-8-sig")
    except Exception as e:  # noqa: BLE001
        return None, f"ファイルを読めませんでした: {e}"
    if not text.strip():
        return [], None
    try:
        data = json.loads(text)
    except json.JSONDecodeError as e:
        return None, (
            "既存の default.json をJSONとして解析できませんでした"
            f"（{e.lineno}行目付近: {e.msg}）。\n"
            "beatoraja本体は末尾カンマ等を許容するため、手書きのファイルは"
            "Pythonの標準JSONで読めない場合があります。")
    if not isinstance(data, list):
        return None, "default.json の最上位がJSON配列ではありません。"
    return data, None


def find_root(folders: list):
    """ROOT_NAME のフォルダの位置を返す。無ければ None。"""
    for i, f in enumerate(folders):
        if isinstance(f, dict) and f.get("name") == ROOT_NAME:
            return i
    return None


def merge_into_root(existing: list, new: list):
    """
    ROOT_NAME のフォルダの中に new を入れる。無ければ先頭に作る。
    同じ名前の子は置き換え、無ければ末尾に足す。
    戻り値 (merged, replaced_names, added_names, root_created)
    """
    merged = [dict(f) if isinstance(f, dict) else f for f in existing]
    idx = find_root(merged)
    created = False

    if idx is None:
        root = {"name": ROOT_NAME, "folder": []}
        merged.insert(0, root)
        idx = 0
        created = True
    else:
        root = merged[idx]
        if not isinstance(root, dict):
            raise ValueError(f"既存の「{ROOT_NAME}」の形式が想定と違います。")
        if root.get("sql") or root.get("rcourse"):
            raise ValueError(
                f"既存の「{ROOT_NAME}」はSQLを直接持つフォルダのため、"
                "中にフォルダを入れられません。名前を変えるか削除してください。")
        root = {"name": ROOT_NAME, "folder": list(root.get("folder") or [])}
        if "showall" in merged[idx]:
            root["showall"] = merged[idx]["showall"]
        merged[idx] = root

    children = root["folder"]
    index = {}
    for i, c in enumerate(children):
        if isinstance(c, dict) and isinstance(c.get("name"), str):
            index[c["name"]] = i

    replaced, added = [], []
    for folder in new:
        nm = folder.get("name")
        if nm in index:
            children[index[nm]] = folder
            replaced.append(nm)
        else:
            index[nm] = len(children)
            children.append(folder)
            added.append(nm)
    return merged, replaced, added, created


def write_default_json(path: Path, folders: list):
    """default.json を書き出す。既存があればバックアップを作る。"""
    path.parent.mkdir(parents=True, exist_ok=True)
    backup = None
    if path.exists():
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        backup = path.with_name(f"{path.name}.{stamp}.bak")
        shutil.copy2(path, backup)
    text = json.dumps(folders, ensure_ascii=False, indent="\t")
    path.write_text(text + "\n", encoding="utf-8")
    return backup


def guess_default_json(base: Path) -> Path:
    """選ばれたパスから folder/default.json の位置を推測する。"""
    if base.is_file() or base.suffix.lower() == ".json":
        # まだ無いファイルを指定された場合もそのまま使う
        return base
    if base.name.lower() == "folder":
        return base / "default.json"
    return base / "folder" / "default.json"


TABLE_STORE_NAME = "difficulty_tables.json"


def app_dir() -> Path:
    """exe または .py が置かれているフォルダ。"""
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


def store_path() -> Path:
    """
    難易度表の保存先を決める。まずアプリと同じフォルダ、
    書き込めなければユーザーフォルダを使う。
    """
    here = app_dir() / TABLE_STORE_NAME
    if here.exists():
        return here
    try:
        probe = app_dir() / (TABLE_STORE_NAME + ".tmp")
        probe.write_text("", encoding="utf-8")
        probe.unlink()
        return here
    except Exception:  # noqa: BLE001
        base = os.environ.get("LOCALAPPDATA") or os.environ.get("XDG_CACHE_HOME")
        root = Path(base) if base else Path.home()
        return root / "beatoraja_folder_maker" / TABLE_STORE_NAME


def new_table_entry(url: str, name: str = "") -> dict:
    return {"url": url, "name": name or url, "tag": "", "symbol": "",
            "header_url": "", "levels": [], "fetched_at": None}


def load_tables() -> tuple:
    """
    保存してある難易度表を読む。戻り値 (tables, removed_urls, message)。
    ファイルが無ければ既定の表を並べて返す。いちど削除した既定の表は戻さない。
    """
    path = store_path()
    tables, removed, msg = [], [], ""
    if path.exists():
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
            for e in data.get("tables") or []:
                url = str(e.get("url") or "").strip()
                if not url:
                    continue
                entry = new_table_entry(url, str(e.get("name") or ""))
                entry["tag"] = str(e.get("tag") or "")
                entry["symbol"] = str(e.get("symbol") or "")
                entry["header_url"] = str(e.get("header_url") or "")
                entry["fetched_at"] = e.get("fetched_at")
                levels = []
                for lv in e.get("levels") or []:
                    levels.append({
                        "level": str(lv.get("level", "")),
                        "label": str(lv.get("label", "")),
                        "md5": [m for m in (lv.get("md5") or [])
                                if MD5_RE.match(str(m))],
                        "sha256": [s for s in (lv.get("sha256") or [])
                                   if SHA256_RE.match(str(s))],
                        "count": int(lv.get("count") or 0),
                    })
                entry["levels"] = levels
                tables.append(entry)
            removed = [str(u) for u in (data.get("removed") or [])]
        except Exception as e:  # noqa: BLE001
            msg = f"難易度表の保存ファイルを読めませんでした（{e}）。既定の表で始めます。"
            tables, removed = [], []

    builtin = dict((url, name) for name, url in BUILTIN_TABLES)
    for t in tables:
        # まだ取得していない既定の表は、表示名を最新の既定値に合わせる
        if not t["levels"] and t["url"] in builtin:
            t["name"] = builtin[t["url"]]

    known = {t["url"] for t in tables} | set(removed)
    for name, url in BUILTIN_TABLES:
        if url not in known:
            tables.append(new_table_entry(url, name))
    return tables, removed, msg


def save_tables(tables: list, removed=()) -> Path:
    """難易度表を保存する。"""
    path = store_path()
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {"version": 1, "saved_at": time.time(),
               "tables": tables, "removed": list(removed)}
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(payload, ensure_ascii=False), encoding="utf-8")
    tmp.replace(path)
    return path


def table_chart_count(entry: dict) -> int:
    return sum(lv.get("count") or 0 for lv in entry.get("levels") or [])


def describe_table(entry: dict) -> str:
    """一覧に出す状態の説明。"""
    if not entry.get("levels"):
        return "未取得"
    when = entry.get("fetched_at")
    stamp = ""
    if when:
        try:
            stamp = datetime.fromtimestamp(float(when)).strftime("%Y-%m-%d")
        except Exception:  # noqa: BLE001
            stamp = ""
    n = table_chart_count(entry)
    lv = len(entry["levels"])
    return f"{n}譜面 / {lv}レベル" + (f" / {stamp} 取得" if stamp else "")


# ===========================================================================
# 譜面数の集計（空フォルダを作らないために使う）
#   beatoraja 本体と同じ形のSELECTを組み、その行数を数える。
#   DBはすべて読み取り専用で開くため、beatoraja のデータを書き換えない。
# ===========================================================================
COUNT_COLUMNS = (
    "md5, song.sha256 AS sha256, title, subtitle, genre, artist, subartist,"
    "path, folder, stagefile, banner, backbmp, parent, song.level AS level,"
    "difficulty, maxbpm, minbpm, song.mode AS mode, judge, feature, content,"
    "song.date AS date, favorite, song.notes AS notes, adddate, preview,"
    "length, charthash")

SCORE_TABLE_DDL = (
    "CREATE TEMP TABLE score (sha256 TEXT, mode INTEGER, clear INTEGER,"
    "epg INTEGER, lpg INTEGER, egr INTEGER, lgr INTEGER, egd INTEGER,"
    "lgd INTEGER, ebd INTEGER, lbd INTEGER, epr INTEGER, lpr INTEGER,"
    "ems INTEGER, lms INTEGER, notes INTEGER, combo INTEGER, minbp INTEGER,"
    "avgjudge INTEGER, playcount INTEGER, clearcount INTEGER, trophy TEXT,"
    "ghost TEXT, option INTEGER, seed INTEGER, random INTEGER, date INTEGER,"
    "state INTEGER, scorehash TEXT)")

SCORELOG_TABLE_DDL = (
    "CREATE TEMP TABLE scorelog (sha256 TEXT, mode INTEGER, clear INTEGER,"
    "oldclear INTEGER, score INTEGER, oldscore INTEGER, combo INTEGER,"
    "oldcombo INTEGER, minbp INTEGER, oldminbp INTEGER, avgjudge INTEGER,"
    "oldavgjudge INTEGER, date INTEGER)")


def beatoraja_root(target: Path) -> Path:
    """folder/default.json から beatoraja のフォルダを割り出す。"""
    parent = target.parent
    return parent.parent if parent.name.lower() == "folder" else parent


def list_players(root: Path) -> list:
    """score.db を持つプレイヤーフォルダの名前を並べる。"""
    base = root / "player"
    if not base.is_dir():
        return []
    names = []
    for p in sorted(base.iterdir()):
        try:
            if p.is_dir() and (p / "score.db").exists():
                names.append(p.name)
        except OSError:
            continue
    return names


def default_player(root: Path, players: list) -> str:
    """config.json に書かれているプレイヤーを優先して選ぶ。"""
    if not players:
        return ""
    cfg = root / "config.json"
    if cfg.exists():
        try:
            data = json.loads(cfg.read_text(encoding="utf-8-sig"))
            name = str(data.get("playername") or "")
            if name in players:
                return name
        except Exception:  # noqa: BLE001
            pass
    return players[0]


def _ro_uri(path: Path) -> str:
    return path.resolve().as_uri() + "?mode=ro"


class ChartCounter:
    """条件に当てはまる譜面の数を数える。使い終わったら close する。"""

    def __init__(self, root: Path, player: str):
        self.root = root
        self.player = player
        self.con = None
        self.notes = []

    def open(self):
        songdb = self.root / "songdata.db"
        if not songdb.exists():
            raise ValueError(f"songdata.db が見つかりません: {songdb}")
        self.con = sqlite3.connect(_ro_uri(songdb), uri=True)
        pdir = self.root / "player" / self.player if self.player else None
        for name, ddl in (("score", SCORE_TABLE_DDL),
                          ("scorelog", SCORELOG_TABLE_DDL)):
            path = (pdir / f"{name}.db") if pdir else None
            if path is not None and path.exists():
                self.con.execute(f"ATTACH DATABASE '{_ro_uri(path)}' AS {name}db")
            else:
                # 無い場合は空のテーブルを作る（未プレイ扱いになる）
                self.con.execute(ddl)
                self.notes.append(f"{name}.db が無いため、スコアなしとして数えます。")
        return self

    def count(self, where: str) -> int:
        sql = ("SELECT COUNT(*) FROM (SELECT DISTINCT " + COUNT_COLUMNS +
               " FROM song AS song LEFT OUTER JOIN (score LEFT OUTER JOIN"
               " scorelog ON score.sha256 = scorelog.sha256)"
               " ON song.sha256 = score.sha256 WHERE " + where + ")")
        return int(self.con.execute(sql).fetchone()[0])

    def close(self):
        if self.con is not None:
            try:
                self.con.close()
            except Exception:  # noqa: BLE001
                pass
            self.con = None


def prune_empty(folders: list, counter: ChartCounter, progress=None) -> tuple:
    """
    譜面が0件のフォルダを取り除く。
    戻り値 (残ったフォルダ, 調べた数, 消した末端の数, 消えた親の数)
    """
    checked = [0]
    gone_leaf = [0]
    gone_dir = [0]

    def walk(nodes):
        kept = []
        for node in nodes:
            if node.get("folder") is not None:
                sub = walk(node["folder"])
                if sub:
                    node["folder"] = sub
                    kept.append(node)
                else:
                    gone_dir[0] += 1
            else:
                checked[0] += 1
                if progress and checked[0] % 50 == 0:
                    progress(checked[0])
                if counter.count(node["sql"]) > 0:
                    kept.append(node)
                else:
                    gone_leaf[0] += 1
        return kept

    return walk(folders), checked[0], gone_leaf[0], gone_dir[0]


def describe_folder(node) -> str:
    """一覧に出す説明文を作る。"""
    if not isinstance(node, dict):
        return "形式が不明"
    if node.get("folder"):
        return f"子フォルダ {len(node['folder'])}件 / 末端 {count_leaves([node])}件"
    if node.get("rcourse"):
        return "ランダムコース"
    if node.get("sql"):
        sql = node["sql"]
        return "SQL: " + (sql[:60] + "…" if len(sql) > 60 else sql)
    return "中身なし"


# ===========================================================================
# GUI 部品
# ===========================================================================
def make_range_tree(master, rows: int, name_w: int = 190, value_w: int = 110):
    """
    「名前 / 下限 / - / 上限」の4列を持つ一覧を作る。
    空白で桁を合わせると、日本語混じりの名前でずれてしまうため、
    表の列そのもので位置を決める。値はすべて左揃え、「-」だけ中央。
    """
    tree = ttk.Treeview(master, columns=("name", "lo", "dash", "hi"),
                        show="", height=rows, selectmode="extended")
    tree.column("name", width=name_w, minwidth=80, anchor="w", stretch=True)
    tree.column("lo", width=value_w, minwidth=40, anchor="w", stretch=False)
    tree.column("dash", width=24, minwidth=24, anchor="center", stretch=False)
    tree.column("hi", width=value_w, minwidth=40, anchor="w", stretch=False)
    return tree


def tree_clear(tree):
    for iid in tree.get_children():
        tree.delete(iid)


def tree_selected_indices(tree) -> list:
    children = list(tree.get_children())
    return sorted(children.index(iid) for iid in tree.selection()
                  if iid in children)


def tree_select_index(tree, index: int):
    children = list(tree.get_children())
    if 0 <= index < len(children):
        tree.selection_set(children[index])


class ScrollFrame(ttk.Frame):
    """縦スクロールする入れ物。"""

    def __init__(self, master):
        super().__init__(master)
        self.canvas = tk.Canvas(self, highlightthickness=0, borderwidth=0)
        vsb = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=vsb.set)
        vsb.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.inner = ttk.Frame(self.canvas, padding=(2, 2))
        self._win = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
        self.inner.bind("<Configure>", self._on_inner)
        self.canvas.bind("<Configure>", self._on_canvas)
        self.canvas.bind("<Enter>", self._bind_wheel)
        self.canvas.bind("<Leave>", self._unbind_wheel)

    def _on_inner(self, _e):
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))

    def _on_canvas(self, e):
        self.canvas.itemconfigure(self._win, width=e.width)

    def _bind_wheel(self, _e):
        self.canvas.bind_all("<MouseWheel>", self._wheel)

    def _unbind_wheel(self, _e):
        self.canvas.unbind_all("<MouseWheel>")

    def _wheel(self, e):
        self.canvas.yview_scroll(int(-e.delta / 120), "units")


class RangeEditor(ttk.Frame):
    """「名前 / 下限 / 上限」のリストを編集する部品。"""

    def __init__(self, master, defaults, unit_label, rows=5, flag_text=None,
                 namer=None):
        super().__init__(master)
        self.defaults = [unpack_range(d) for d in defaults]
        self.flag_var = tk.BooleanVar(value=False) if flag_text else None
        self.flag_text = flag_text or ""
        self.namer = namer

        self.tree = make_range_tree(self, rows)
        self.tree.grid(row=0, column=0, sticky="nsew")
        sb = ttk.Scrollbar(self, orient="vertical", command=self.tree.yview)
        sb.grid(row=0, column=1, sticky="ns")
        self.tree.configure(yscrollcommand=sb.set)

        form = ttk.Frame(self)
        form.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(6, 0))
        ttk.Label(form, text="名前").grid(row=0, column=0, padx=(0, 4))
        self.e_name = ttk.Entry(form, width=16)
        self.e_name.grid(row=0, column=1, padx=(0, 8))
        ttk.Label(form, text=f"{unit_label} 下限").grid(row=0, column=2, padx=(0, 4))
        self.e_lo = ttk.Entry(form, width=6)
        self.e_lo.grid(row=0, column=3, padx=(0, 8))
        ttk.Label(form, text="上限").grid(row=0, column=4, padx=(0, 4))
        self.e_hi = ttk.Entry(form, width=6)
        self.e_hi.grid(row=0, column=5, padx=(0, 8))
        col = 6
        if self.flag_var is not None:
            ttk.Checkbutton(form, text=flag_text, variable=self.flag_var).grid(
                row=0, column=col, padx=(0, 8))
            col += 1
        ttk.Button(form, text="追加", width=6, command=self.add).grid(
            row=0, column=col)
        ttk.Button(form, text="削除", width=6, command=self.remove).grid(
            row=0, column=col + 1, padx=(4, 0))
        ttk.Button(form, text="↑", width=3, command=lambda: self.move(-1)).grid(
            row=0, column=col + 2, padx=(4, 0))
        ttk.Button(form, text="↓", width=3, command=lambda: self.move(1)).grid(
            row=0, column=col + 3, padx=(2, 0))
        ttk.Button(form, text="初期値", width=7, command=self.reset).grid(
            row=0, column=col + 4, padx=(4, 0))

        self.columnconfigure(0, weight=1)
        self.items = []
        self.reset()

    def _refresh(self):
        tree_clear(self.tree)
        for nm, lo, hi, flag in self.items:
            if flag:
                self.tree.insert("", "end",
                                 values=(nm, self.flag_text, "", ""))
                continue
            lo_s = "" if lo is None else str(lo)
            hi_s = "" if hi is None else str(hi)
            self.tree.insert("", "end", values=(nm, lo_s, "-", hi_s))

    @staticmethod
    def _parse(s):
        s = s.strip()
        return None if not s else int(s)

    def reset(self):
        self.items = list(self.defaults)
        if self.flag_var is not None:
            self.flag_var.set(False)
        self._refresh()

    def add(self):
        name = self.e_name.get().strip()
        flag = bool(self.flag_var.get()) if self.flag_var is not None else False
        try:
            lo = self._parse(self.e_lo.get())
            hi = self._parse(self.e_hi.get())
        except ValueError:
            messagebox.showwarning(APP_TITLE, "下限・上限は整数で入れてください。")
            return
        if flag:
            # 変化ありのときは下限・上限を使わない
            lo = hi = None
        else:
            if lo is None and hi is None:
                messagebox.showwarning(APP_TITLE, "下限か上限のどちらかは入れてください。")
                return
            if lo is not None and hi is not None and lo > hi:
                messagebox.showwarning(APP_TITLE, "下限が上限を超えています。")
                return
        if not name:
            # 名前を空にしたときは下限・上限から自動で付ける
            name = self.namer(lo, hi, flag) if self.namer else ""
            if not name:
                messagebox.showwarning(APP_TITLE, "名前を入れてください。")
                return
        self.items.append((name, lo, hi, flag))
        self._refresh()
        for e in (self.e_name, self.e_lo, self.e_hi):
            e.delete(0, "end")
        if self.flag_var is not None:
            self.flag_var.set(False)

    def remove(self):
        for i in reversed(tree_selected_indices(self.tree)):
            del self.items[i]
        self._refresh()

    def move(self, delta):
        sel = tree_selected_indices(self.tree)
        if not sel:
            return
        i = sel[0]
        j = i + delta
        if not (0 <= j < len(self.items)):
            return
        self.items[i], self.items[j] = self.items[j], self.items[i]
        self._refresh()
        tree_select_index(self.tree, j)

    def get_ranges(self):
        return list(self.items)


class RankEditor(ttk.Frame):
    """「名前 / 下限ランク / 上限ランク」のリストを編集する部品。"""

    def __init__(self, master, defaults, values, rows=4):
        super().__init__(master)
        self.defaults = [tuple(d) for d in defaults]
        self.values = list(values)
        self.tree = make_range_tree(self, rows)
        self.tree.grid(row=0, column=0, sticky="nsew")
        sb = ttk.Scrollbar(self, orient="vertical", command=self.tree.yview)
        sb.grid(row=0, column=1, sticky="ns")
        self.tree.configure(yscrollcommand=sb.set)

        form = ttk.Frame(self)
        form.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(6, 0))
        ttk.Label(form, text="名前").grid(row=0, column=0, padx=(0, 4))
        self.e_name = ttk.Entry(form, width=16)
        self.e_name.grid(row=0, column=1, padx=(0, 8))
        ttk.Label(form, text="下限").grid(row=0, column=2, padx=(0, 4))
        self.c_lo = ttk.Combobox(form, values=self.values, width=5,
                                 state="readonly")
        self.c_lo.grid(row=0, column=3, padx=(0, 8))
        ttk.Label(form, text="上限").grid(row=0, column=4, padx=(0, 4))
        self.c_hi = ttk.Combobox(form, values=self.values, width=5,
                                 state="readonly")
        self.c_hi.grid(row=0, column=5, padx=(0, 8))
        ttk.Button(form, text="追加", width=6, command=self.add).grid(
            row=0, column=6)
        ttk.Button(form, text="削除", width=6, command=self.remove).grid(
            row=0, column=7, padx=(4, 0))
        ttk.Button(form, text="↑", width=3, command=lambda: self.move(-1)).grid(
            row=0, column=8, padx=(4, 0))
        ttk.Button(form, text="↓", width=3, command=lambda: self.move(1)).grid(
            row=0, column=9, padx=(2, 0))
        ttk.Button(form, text="初期値", width=7, command=self.reset).grid(
            row=0, column=10, padx=(4, 0))

        self.columnconfigure(0, weight=1)
        self.items = []
        self.c_lo.set(self.values[0])
        self.c_hi.set(self.values[-1])
        self.reset()

    def _refresh(self):
        tree_clear(self.tree)
        for nm, lo, hi in self.items:
            self.tree.insert("", "end", values=(nm, lo, "-", hi))

    def reset(self):
        self.items = list(self.defaults)
        self._refresh()

    def add(self):
        name = self.e_name.get().strip()
        lo, hi = self.c_lo.get().strip(), self.c_hi.get().strip()
        if not name:
            messagebox.showwarning(APP_TITLE, "名前を入れてください。")
            return
        if lo not in self.values or hi not in self.values:
            messagebox.showwarning(APP_TITLE, "下限と上限を選んでください。")
            return
        if self.values.index(lo) > self.values.index(hi):
            messagebox.showwarning(APP_TITLE, "下限が上限を超えています。")
            return
        self.items.append((name, lo, hi))
        self._refresh()
        self.e_name.delete(0, "end")

    def remove(self):
        for i in reversed(tree_selected_indices(self.tree)):
            del self.items[i]
        self._refresh()

    def move(self, delta):
        sel = tree_selected_indices(self.tree)
        if not sel:
            return
        i = sel[0]
        j = i + delta
        if not (0 <= j < len(self.items)):
            return
        self.items[i], self.items[j] = self.items[j], self.items[i]
        self._refresh()
        tree_select_index(self.tree, j)

    def get_ranges(self):
        return list(self.items)


class Section(ttk.LabelFrame):
    """見出し付きの区画。"""

    def __init__(self, master, title, var, toggle_text):
        super().__init__(master, text=title, padding=10)
        self.body = ttk.Frame(self)
        ttk.Checkbutton(self, text=toggle_text, variable=var).pack(anchor="w")
        self.body.pack(fill="both", expand=True, pady=(6, 0))


# ===========================================================================
# 本体
# ===========================================================================
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.geometry("900x760")
        self.minsize(840, 640)

        self.tables, self.removed_urls, load_msg = load_tables()
        # 画面を組み立てる前に用意しておく（組み立ての途中で参照されるため）
        self.path_var = tk.StringVar()
        self.tbl_url_var = tk.StringVar()
        self.hint_var = tk.StringVar()
        self.new_url = tk.StringVar()
        self.title_var = tk.StringVar()
        self.status = tk.StringVar(value="準備完了")
        self.list_info = tk.StringVar(
            value="ファイルを指定して「読み込む」を押してください。")
        self.tbl_enabled = tk.BooleanVar(value=True)
        self.bpm_enabled = tk.BooleanVar(value=False)
        self.bp_enabled = tk.BooleanVar(value=True)
        self.bp_noplay = tk.BooleanVar(value=True)
        self.lamp_enabled = tk.BooleanVar(value=False)
        self.score_enabled = tk.BooleanVar(value=False)
        self.split_levels = tk.BooleanVar(value=False)
        self.skip_empty = tk.BooleanVar(value=True)
        self.player_var = tk.StringVar()
        self.msg_queue: queue.Queue = queue.Queue()
        self.list_rows: list = []

        self._build_ui()
        self.after(100, self._drain_queue)
        if load_msg:
            self.log(load_msg)
        self.log(f"難易度表の保存先: {store_path()}")

    # -- UI -----------------------------------------------------------------
    def _build_ui(self):
        top = ttk.Frame(self, padding=(10, 10, 10, 0))
        top.pack(fill="x")
        ttk.Label(
            top,
            text="beatoraja本体と同じ場所にある「folder」フォルダ"
                 "（この中の default.json を書き換えます）").pack(anchor="w")
        row = ttk.Frame(top)
        row.pack(fill="x", pady=(4, 0))
        ttk.Entry(row, textvariable=self.path_var).pack(
            side="left", fill="x", expand=True)
        ttk.Button(row, text="folderを選ぶ…", command=self._choose_dir).pack(
            side="left", padx=(6, 0))
        ttk.Button(row, text="default.jsonを直接指定…", command=self._choose_file).pack(
            side="left", padx=(6, 0))

        self.nb = ttk.Notebook(self)
        self.nb.pack(fill="both", expand=True, padx=10, pady=(10, 0))
        self._build_make_tab()
        self._build_list_tab()

        ttk.Label(self, textvariable=self.status, anchor="w",
                  padding=(12, 6)).pack(fill="x")

    def _build_make_tab(self):
        outer = ttk.Frame(self.nb)
        self.nb.add(outer, text="フォルダを作る")
        sf = ScrollFrame(outer)
        sf.pack(fill="both", expand=True)
        page = sf.inner

        # --- 1. 難易度表 ---
        s1 = Section(page, "1. 難易度表", self.tbl_enabled, "難易度表で絞る")
        s1.pack(fill="x", padx=6, pady=(6, 0))
        b = s1.body
        ttk.Label(b, text="使う難易度表を選ぶ（Ctrl・Shiftで複数選択）").pack(anchor="w")
        lf = ttk.Frame(b)
        lf.pack(fill="x", pady=(4, 0))
        self.tbl_list = tk.Listbox(lf, selectmode="extended", height=5,
                                   exportselection=False)
        self.tbl_list.pack(side="left", fill="both", expand=True)
        sb = ttk.Scrollbar(lf, orient="vertical", command=self.tbl_list.yview)
        sb.pack(side="left", fill="y")
        self.tbl_list.configure(yscrollcommand=sb.set)
        self._refresh_table_list()
        if self.tables:
            self.tbl_list.selection_set(0)
        self.tbl_list.bind("<<ListboxSelect>>", lambda _e: self._on_table_select())
        self._on_table_select()

        ttk.Label(b, textvariable=self.tbl_url_var, foreground="#555").pack(
            anchor="w", pady=(2, 0))

        opf = ttk.Frame(b)
        opf.pack(fill="x", pady=(6, 0))
        ttk.Button(opf, text="選択した表を取得 / 更新",
                   command=self._fetch_tables).pack(side="left")
        ttk.Button(opf, text="選択した表を削除",
                   command=self._del_table).pack(side="left", padx=(6, 0))
        ttk.Label(opf, text="取得した表は保存され、次に起動したときもそのまま使えます。",
                  foreground="#555").pack(side="left", padx=(12, 0))

        addf = ttk.Frame(b)
        addf.pack(fill="x", pady=(6, 0))
        ttk.Label(addf, text="表を追加（表のページURL / header.json のURL）").grid(
            row=0, column=0, columnspan=2, sticky="w")
        ttk.Entry(addf, textvariable=self.new_url).grid(
            row=1, column=0, sticky="ew", pady=(4, 0))
        ttk.Button(addf, text="追加", command=self._add_table).grid(
            row=1, column=1, padx=(6, 0), pady=(4, 0))
        addf.columnconfigure(0, weight=1)

        ttk.Checkbutton(
            b, text="最下層を難易度レベルにする（各フォルダの中に sl0・★1 などを作る）",
            variable=self.split_levels).pack(anchor="w", pady=(8, 0))

        # --- 2. BPM ---
        s2 = Section(page, "2. BPM", self.bpm_enabled, "BPMで絞る")
        s2.pack(fill="x", padx=6, pady=(10, 0))
        b = s2.body
        self.bpm_editor = RangeEditor(b, DEFAULT_BPM_RANGES, "BPM", rows=6,
                                      flag_text="BPM変化あり",
                                      namer=bpm_name)
        self.bpm_editor.pack(fill="x")
        ttk.Label(b, text="名前を空にして「追加」すると、下限・上限から自動で名前を付けます。"
                          "song.minbpm >= 下限 AND song.maxbpm <= 上限 になります。"
                          "「BPM変化あり」を付けた行は下限・上限を無視して、"
                          "song.minbpm != song.maxbpm になります。",
                  foreground="#555", wraplength=800, justify="left").pack(
            anchor="w", pady=(6, 0))

        # --- 3. BP ---
        s3 = Section(page, "3. BP", self.bp_enabled, "BPで絞る")
        s3.pack(fill="x", padx=6, pady=(10, 0))
        b = s3.body
        r = ttk.Frame(b)
        r.pack(fill="x")
        ttk.Checkbutton(r, text="「未プレイ」も作る", variable=self.bp_noplay).pack(
            side="left")
        self.bp_editor = RangeEditor(b, DEFAULT_BP_RANGES, "BP", rows=6,
                                     namer=lambda lo, hi, flag: bp_name(lo, hi))
        self.bp_editor.pack(fill="x", pady=(6, 0))
        ttk.Label(b, text="自己ベストの最小BAD+POOR（score.minbp）で絞ります。"
                          "プレイ済みの譜面だけが対象です。"
                          "名前を空にして「追加」すると自動で名前を付けます。",
                  foreground="#555").pack(anchor="w", pady=(6, 0))

        # --- 4. LAMP ---
        s34 = Section(page, "4. LAMP", self.lamp_enabled, "クリアランプで絞る")
        s34.pack(fill="x", padx=6, pady=(10, 0))
        b = s34.body
        self.lamp_editor = RankEditor(b, DEFAULT_LAMP_RANGES, LAMP_NAMES, rows=8)
        self.lamp_editor.pack(fill="x")
        ttk.Label(b, text="自己ベストのクリアランプ（score.clear）で絞ります。"
                          "下限・上限は NO PLAY FAILED ASSIST L-ASSIST EASY "
                          "CLEAR HARD EX-HARD FULLCOMBO PERFECT MAX から選びます。"
                          "未プレイの譜面はどのランプにも入りません。",
                  foreground="#555", wraplength=800, justify="left").pack(
            anchor="w", pady=(6, 0))

        # --- 5. SCORE ---
        s35 = Section(page, "5. SCORE", self.score_enabled, "DJ LEVELで絞る")
        s35.pack(fill="x", padx=6, pady=(10, 0))
        b = s35.body
        self.score_editor = RankEditor(b, DEFAULT_SCORE_RANGES, DJ_LEVELS)
        self.score_editor.pack(fill="x")
        ttk.Label(b, text="自己ベストのDJ LEVELで絞ります。EXスコア（PGREAT2点 + "
                          "GREAT1点）とノート数から出すため、プレイ済みの譜面だけが"
                          "対象です。下限・上限は F E D C B A AA AAA から選びます。",
                  foreground="#555", wraplength=800, justify="left").pack(
            anchor="w", pady=(6, 0))

        # --- 6. 生成 ---
        s4 = ttk.LabelFrame(page, text="6. 生成", padding=10)
        s4.pack(fill="both", expand=True, padx=6, pady=(10, 10))
        tf = ttk.Frame(s4)
        tf.pack(fill="x")
        ttk.Label(tf, text="フォルダ名").pack(side="left")
        ttk.Entry(tf, textvariable=self.title_var).pack(
            side="left", fill="x", expand=True, padx=(8, 0))
        ttk.Label(s4, textvariable=self.hint_var, foreground="#555").pack(
            anchor="w", pady=(4, 0))

        ef = ttk.Frame(s4)
        ef.pack(fill="x", pady=(8, 0))
        ttk.Checkbutton(ef, text="譜面が0件のフォルダを作らない",
                        variable=self.skip_empty).pack(side="left")
        ttk.Label(ef, text="プレイヤー").pack(side="left", padx=(16, 4))
        self.player_box = ttk.Combobox(ef, textvariable=self.player_var,
                                       width=18, state="readonly")
        self.player_box.pack(side="left")
        ttk.Label(ef, text="songdata.db と score.db を読み取り専用で開いて数えます。",
                  foreground="#555").pack(side="left", padx=(10, 0))
        for var in (self.tbl_enabled, self.bpm_enabled, self.bp_enabled,
                    self.lamp_enabled, self.score_enabled):
            var.trace_add("write", lambda *_a: self._update_hint())
        self._update_hint()

        bar = ttk.Frame(s4)
        bar.pack(fill="x", pady=(8, 0))
        self.btn_preview = ttk.Button(bar, text="プレビュー（書き込まない）",
                                      command=lambda: self._run(False))
        self.btn_preview.pack(side="left")
        self.btn_write = ttk.Button(bar, text="生成して書き込む",
                                    command=lambda: self._run(True))
        self.btn_write.pack(side="left", padx=(8, 0))
        ttk.Button(bar, text="ログを消す",
                   command=lambda: self.log_text.delete("1.0", "end")).pack(
            side="right")

        logf = ttk.Frame(s4)
        logf.pack(fill="both", expand=True, pady=(8, 0))
        self.log_text = tk.Text(logf, height=12, wrap="none",
                                font=("Consolas", 10))
        self.log_text.pack(side="left", fill="both", expand=True)
        lsb = ttk.Scrollbar(logf, orient="vertical", command=self.log_text.yview)
        lsb.pack(side="left", fill="y")
        self.log_text.configure(yscrollcommand=lsb.set)

    def _build_list_tab(self):
        outer = ttk.Frame(self.nb, padding=10)
        self.nb.add(outer, text="生成したフォルダ")

        bar = ttk.Frame(outer)
        bar.pack(fill="x")
        ttk.Button(bar, text="読み込む / 再読込", command=self.reload_list).pack(
            side="left")
        ttk.Label(bar, textvariable=self.list_info, foreground="#555").pack(
            side="left", padx=(12, 0))

        head = ttk.Frame(outer)
        head.pack(fill="x", pady=(10, 2))
        ttk.Label(head, text="フォルダ名", width=36).pack(side="left")
        ttk.Label(head, text="中身").pack(side="left")
        ttk.Separator(outer, orient="horizontal").pack(fill="x")

        self.list_frame = ScrollFrame(outer)
        self.list_frame.pack(fill="both", expand=True, pady=(4, 0))

        ttk.Label(outer, text="削除するとバックアップを作ってから default.json を"
                              "書き換えます。beatoraja の再起動が必要です。",
                  foreground="#555").pack(anchor="w", pady=(8, 0))

    # -- 小物 ---------------------------------------------------------------
    def _refresh_table_list(self, keep_urls=None):
        if keep_urls is None:
            keep_urls = self._selected_urls()
        self.tbl_list.delete(0, "end")
        for entry in self.tables:
            self.tbl_list.insert("end",
                                 f"{entry['name']}   ｜ {describe_table(entry)}")
        for i, entry in enumerate(self.tables):
            if entry["url"] in keep_urls:
                self.tbl_list.selection_set(i)
        self._on_table_select()

    def _selected_urls(self):
        return [self.tables[i]["url"] for i in self.tbl_list.curselection()
                if 0 <= i < len(self.tables)]

    def _selected_entries(self):
        return [self.tables[i] for i in self.tbl_list.curselection()
                if 0 <= i < len(self.tables)]

    def _on_table_select(self):
        sel = self._selected_entries()
        if len(sel) == 1:
            self.tbl_url_var.set(sel[0]["url"])
        elif sel:
            self.tbl_url_var.set(f"{len(sel)}件を選択中")
        else:
            self.tbl_url_var.set("")
        self._update_hint()

    def _fetch_tables(self):
        """選んだ表をいま取得（または取り直し）して保存する。"""
        urls = self._selected_urls()
        if not urls:
            messagebox.showwarning(APP_TITLE, "取得する表を選んでください。")
            return
        self.btn_preview.state(["disabled"])
        self.btn_write.state(["disabled"])
        threading.Thread(target=self._fetch_worker, args=(urls, True),
                         daemon=True).start()

    def _fetch_worker(self, urls, force):
        try:
            for url in urls:
                entry = self._entry_of(url)
                if entry is None:
                    continue
                if entry["levels"] and not force:
                    continue
                self.set_status(f"取得中… {entry['name']}")
                self.log(f"[難易度表] 取得: {url}")
                self._store_table(entry, load_table(url))
                self.log(f"  {entry['name']}（記号 {entry['tag'] or '-'}） "
                         f"レベル {len(entry['levels'])}種 / "
                         f"譜面 {table_chart_count(entry)}件")
            path = self._save_tables()
            self.log(f"保存しました: {path}")
            self.set_status("取得しました")
        except Exception as e:  # noqa: BLE001
            self.log("―― エラー ――\n" + traceback.format_exc())
            self.msg_queue.put(("error", str(e)))
            self.set_status("取得に失敗しました")
        finally:
            self.msg_queue.put(("tables", None))
            self.msg_queue.put(("done", None))

    def _save_tables(self):
        return save_tables(self.tables, self.removed_urls)

    def _entry_of(self, url):
        for entry in self.tables:
            if entry["url"] == url:
                return entry
        return None

    @staticmethod
    def _store_table(entry, table):
        entry["name"] = table["name"]
        entry["tag"] = table["tag"]
        entry["symbol"] = table["symbol"]
        entry["header_url"] = table["header_url"]
        entry["levels"] = table["levels"]
        entry["fetched_at"] = time.time()

    def _selected_table_names(self):
        """一覧で選ばれている表の表示名を返す。"""
        if not self.tbl_enabled.get():
            return []
        return [e["name"] for e in self._selected_entries()]

    def _update_hint(self):
        """フォルダ名を未入力にしたときの名前を案内する。"""
        name = auto_title(self._selected_table_names(),
                          bool(self.bpm_enabled.get()),
                          bool(self.bp_enabled.get()),
                          bool(self.lamp_enabled.get()),
                          bool(self.score_enabled.get()))
        if name:
            self.hint_var.set(f"未入力なら「{name}」になります")
        else:
            self.hint_var.set("条件を選ぶと、未入力のときの名前がここに出ます")

    def _choose_dir(self):
        d = filedialog.askdirectory(
            title="beatoraja本体と同じ場所にある folder フォルダを選ぶ")
        if d:
            self.path_var.set(str(guess_default_json(Path(d))))
            self.reload_list()

    def _choose_file(self):
        f = filedialog.askopenfilename(
            title="default.json を選ぶ",
            filetypes=[("JSON", "*.json"), ("すべて", "*.*")])
        if f:
            self.path_var.set(f)
            self.reload_list()

    def _add_table(self):
        url = self.new_url.get().strip()
        if not url:
            return
        if not url.lower().startswith(("http://", "https://")):
            messagebox.showwarning(APP_TITLE, "http:// または https:// のURLを入れてください。")
            return
        if self._entry_of(url) is not None:
            messagebox.showinfo(APP_TITLE, "その表はすでに一覧にあります。")
            return
        self.tables.append(new_table_entry(url))
        if url in self.removed_urls:
            self.removed_urls.remove(url)
        self._save_tables()
        self._refresh_table_list(keep_urls=[url])
        self.new_url.set("")
        self.log(f"難易度表を一覧に追加しました: {url}")
        self.log("「選択した表を取得 / 更新」を押すと、いま取得して保存します。")

    def _del_table(self):
        entries = self._selected_entries()
        if not entries:
            messagebox.showwarning(APP_TITLE, "削除する表を選んでください。")
            return
        names = "\n".join("・" + e["name"] for e in entries)
        if not messagebox.askyesno(
                APP_TITLE,
                f"次の難易度表を一覧から削除します。\n\n{names}\n\n"
                "保存してあるデータも消えます。"
                "既に作ったフォルダはそのまま残ります。\nよろしいですか？"):
            return
        gone = {e["url"] for e in entries}
        builtin = {u for _n, u in BUILTIN_TABLES}
        for url in gone:
            if url in builtin and url not in self.removed_urls:
                self.removed_urls.append(url)
        self.tables = [t for t in self.tables if t["url"] not in gone]
        self._save_tables()
        self._refresh_table_list(keep_urls=[])
        for e in entries:
            self.log(f"難易度表を削除しました: {e['name']}")
        self.set_status(f"{len(entries)}件の難易度表を削除しました")

    def log(self, msg: str):
        self.msg_queue.put(("log", msg))

    def set_status(self, msg: str):
        self.msg_queue.put(("status", msg))

    def _drain_queue(self):
        try:
            while True:
                kind, payload = self.msg_queue.get_nowait()
                if kind == "log":
                    self.log_text.insert("end", payload + "\n")
                    self.log_text.see("end")
                elif kind == "status":
                    self.status.set(payload)
                elif kind == "done":
                    self.btn_preview.state(["!disabled"])
                    self.btn_write.state(["!disabled"])
                elif kind == "error":
                    messagebox.showerror(APP_TITLE, payload)
                elif kind == "refresh":
                    self._refresh_table_list()
                    self.reload_list()
                elif kind == "tables":
                    self._refresh_table_list()
        except queue.Empty:
            pass
        self.after(100, self._drain_queue)

    def _target(self):
        s = self.path_var.get().strip()
        if not s:
            return None
        return guess_default_json(Path(s))

    # -- 「生成したフォルダ」タブ -------------------------------------------
    def refresh_players(self):
        """beatoraja のフォルダからプレイヤー一覧を読み直す。"""
        target = self._target()
        players = list_players(beatoraja_root(target)) if target else []
        try:
            self.player_box.configure(values=players)
        except Exception:  # noqa: BLE001
            pass
        if self.player_var.get() not in players:
            self.player_var.set(default_player(beatoraja_root(target), players)
                                if target else "")

    def reload_list(self):
        self.refresh_players()
        for w in self.list_frame.inner.winfo_children():
            w.destroy()
        self.list_rows = []

        target = self._target()
        if target is None:
            self.list_info.set("beatoraja のフォルダを指定してください。")
            return
        if not target.exists():
            self.list_info.set(f"まだファイルがありません（{target}）")
            ttk.Label(self.list_frame.inner,
                      text="default.json がありません。フォルダを生成すると作られます。",
                      foreground="#555").pack(anchor="w", pady=6)
            return

        folders, err = read_existing(target)
        if folders is None:
            self.list_info.set("読み込めませんでした")
            ttk.Label(self.list_frame.inner, text=err, foreground="#a00",
                      wraplength=780, justify="left").pack(anchor="w", pady=6)
            return

        self.list_info.set(f"トップレベル {len(folders)}件（{target}）")
        if not folders:
            ttk.Label(self.list_frame.inner, text="フォルダはまだありません。",
                      foreground="#555").pack(anchor="w", pady=6)
            return

        root_idx = find_root(folders)

        def add_row(label, desc, path, indent=0, bold=False):
            row = ttk.Frame(self.list_frame.inner)
            row.pack(fill="x", pady=1)
            ttk.Label(row, text=("    " * indent) + label, width=36,
                      anchor="w", font=("", 9, "bold") if bold else "").pack(
                side="left")
            ttk.Label(row, text=desc, anchor="w", foreground="#555").pack(
                side="left", fill="x", expand=True)
            ttk.Button(row, text="削除", width=6,
                       command=lambda pth=path: self._delete_row(pth)).pack(
                side="right")
            self.list_rows.append(path)

        if root_idx is not None:
            root = folders[root_idx]
            children = root.get("folder") or []
            add_row(ROOT_NAME, f"中身 {len(children)}件（まとめて削除）",
                    [root_idx], bold=True)
            if not children:
                ttk.Label(self.list_frame.inner,
                          text="        （中身はまだありません）",
                          foreground="#555").pack(anchor="w")
            for j, child in enumerate(children):
                nm = child.get("name", "（名前なし）") \
                    if isinstance(child, dict) else "?"
                add_row(nm, describe_folder(child), [root_idx, j], indent=1)

        others = [(i, f) for i, f in enumerate(folders) if i != root_idx]
        if others:
            ttk.Label(self.list_frame.inner,
                      text=f"── {ROOT_NAME} 以外のトップレベル ──",
                      foreground="#555").pack(anchor="w", pady=(10, 2))
            for i, node in others:
                nm = node.get("name", "（名前なし）") \
                    if isinstance(node, dict) else "?"
                add_row(nm, describe_folder(node), [i])

    def _delete_row(self, path: list):
        target = self._target()
        if target is None:
            return
        folders, err = read_existing(target)
        if folders is None:
            messagebox.showerror(APP_TITLE, err)
            return

        node, parent = None, folders
        try:
            for depth, i in enumerate(path):
                node = parent[i]
                if depth < len(path) - 1:
                    parent = node["folder"]
        except (IndexError, KeyError, TypeError):
            messagebox.showinfo(APP_TITLE, "一覧が古くなっています。読み込み直します。")
            self.reload_list()
            return

        name = node.get("name", "（名前なし）") if isinstance(node, dict) else "?"
        extra = ""
        if isinstance(node, dict) and node.get("folder"):
            extra = f"\n中身の {len(node['folder'])}件も一緒に消えます。"
        if not messagebox.askyesno(
                APP_TITLE,
                f"「{name}」を default.json から削除します。{extra}\nよろしいですか？"):
            return

        del parent[path[-1]]
        backup = write_default_json(target, folders)
        self.log(f"削除: {name}")
        if backup:
            self.log(f"バックアップ: {backup.name}")
        self.set_status(f"「{name}」を削除しました")
        self.reload_list()

    # -- 生成 ---------------------------------------------------------------
    def _run(self, write: bool):
        target = self._target()
        if target is None:
            messagebox.showwarning(APP_TITLE, "beatoraja のフォルダを指定してください。")
            return

        selected = self._selected_urls() if self.tbl_enabled.get() else []
        if self.tbl_enabled.get() and not selected:
            messagebox.showwarning(APP_TITLE, "難易度表を1つ以上選ぶか、"
                                              "「難易度表で絞る」のチェックを外してください。")
            return

        params = {
            "target": target,
            "write": write,
            "tables": selected,
            "title": self.title_var.get().strip(),
            "bpm": (self.bpm_enabled.get(), self.bpm_editor.get_ranges()),
            "bp": (self.bp_enabled.get(), self.bp_editor.get_ranges(),
                   self.bp_noplay.get()),
            "lamp": (self.lamp_enabled.get(), self.lamp_editor.get_ranges()),
            "score": (self.score_enabled.get(),
                      self.score_editor.get_ranges()),
            "split_levels": self.split_levels.get(),
            "skip_empty": self.skip_empty.get(),
            "player": self.player_var.get(),
        }
        self.btn_preview.state(["disabled"])
        self.btn_write.state(["disabled"])
        threading.Thread(target=self._worker, args=(params,), daemon=True).start()

    def _worker(self, p):
        try:
            self._do_work(p)
        except Exception as e:  # noqa: BLE001
            self.log("―― エラー ――\n" + traceback.format_exc())
            self.msg_queue.put(("error", str(e)))
        finally:
            self.msg_queue.put(("done", None))
            self.set_status("待機中")

    def _do_work(self, p):
        target: Path = p["target"]
        self.log("=" * 72)
        self.log(f"対象ファイル: {target}")

        use_bpm = p["bpm"][0] and p["bpm"][1]
        use_bp = p["bp"][0] and (p["bp"][1] or p["bp"][2])
        use_lamp = p["lamp"][0] and p["lamp"][1]
        use_score = p["score"][0] and p["score"][1]
        if not (p["tables"] or use_bpm or use_bp or use_lamp or use_score):
            self.log("条件が1つも選ばれていません。")
            return

        tables, fetched_any = [], False
        for url in p["tables"]:
            entry = self._entry_of(url)
            if entry is None:
                continue
            if not entry["levels"]:
                self.set_status(f"難易度表を取得中… {entry['name']}")
                self.log(f"[難易度表] 取得: {url}")
                self._store_table(entry, load_table(url))
                fetched_any = True
            else:
                self.log(f"[難易度表] 保存済みのデータを使います: {entry['name']}")
            self.log(f"  {entry['name']}（記号 {entry['tag'] or '-'}） "
                     f"レベル {len(entry['levels'])}種 / "
                     f"譜面 {table_chart_count(entry)}件")
            tables.append(entry)

        if fetched_any:
            self.log(f"難易度表を保存しました: {self._save_tables()}")
            self.msg_queue.put(("tables", None))

        new_folders = build_folder(tables, p["bpm"], p["bp"], p["lamp"],
                                   p["score"], p["title"], p["split_levels"])
        if not new_folders:
            self.log("生成する対象がありません。")
            return

        problems = validate_folders(new_folders)
        if problems:
            for msg in problems:
                self.log("  ! " + msg)
            raise ValueError("生成したフォルダ定義に問題があります。ログを確認してください。")

        if p["skip_empty"]:
            self._prune(new_folders, p)

        for f in new_folders:
            children = f.get("folder") or []
            self.log(f"\n作られるフォルダ: {ROOT_NAME} > {f['name']}"
                     f"（中身 {len(children)}件）")
            self._log_leaves(children, limit=10)

        if not (new_folders and (new_folders[0].get("folder") or [])):
            self.log("\n条件に当てはまる譜面が1つもありませんでした。"
                     "条件を見直すか、「譜面が0件のフォルダを作らない」を外してください。")
            return

        existing, err = read_existing(target)
        if existing is None:
            self.log("\n" + err)
            if p["write"]:
                raise ValueError(err + "\n\n既存ファイルを読めないため書き込みを"
                                       "中止しました。退避してから再実行してください。")
            existing = []
            self.log("（プレビューのため、既存なしとして続けます）")

        merged, replaced, added, created = merge_into_root(existing, new_folders)
        self.log(f"\n既存のトップレベルフォルダ: {len(existing)}件")
        if created:
            self.log(f"「{ROOT_NAME}」を先頭に作りました。")
        if replaced:
            self.log("同名のため置き換え: " + ", ".join(replaced))
        if added:
            self.log("新規に追加: " + ", ".join(added))

        text = json.dumps(merged, ensure_ascii=False, indent="\t")
        size = len(text.encode("utf-8"))
        self.log(f"生成後のファイルサイズ: 約 {size / 1024:.1f} KB "
                 f"/ 末端フォルダ 合計 {count_leaves(merged)}件")

        if not p["write"]:
            if size > SIZE_WARN:
                self.log("※ かなり大きくなります。beatoraja の起動が遅くなる場合は"
                         "条件を減らしてください。")
            self.log("\nプレビューのみです。ファイルは書き換えていません。")
            self.set_status("プレビュー完了")
            return

        if size > SIZE_WARN:
            ok = messagebox.askyesno(
                APP_TITLE,
                f"生成後のファイルが約 {size / 1024 / 1024:.1f} MB になります。\n"
                "beatoraja の起動が遅くなる可能性があります。続けますか？")
            if not ok:
                self.log("中止しました。")
                self.set_status("中止")
                return

        backup = write_default_json(target, merged)
        if backup:
            self.log(f"バックアップ: {backup.name}")
        self.log(f"書き込み完了: {target}")
        self.log("beatoraja を再起動すると選曲画面に反映されます。")
        self.set_status("書き込み完了")
        self.msg_queue.put(("refresh", None))

    def _prune(self, folders, p):
        """譜面数を数えて、0件のフォルダを取り除く。失敗しても生成は続ける。"""
        root = beatoraja_root(p["target"])
        counter = ChartCounter(root, p["player"])
        total = count_leaves(folders)
        started = time.time()
        try:
            counter.open()
        except Exception as e:  # noqa: BLE001
            self.log(f"\n譜面数を数えられませんでした（{e}）。"
                     "0件のフォルダもそのまま作ります。")
            return
        for note in counter.notes:
            self.log("  " + note)
        self.log(f"\n譜面数を数えています（{total}件）… "
                 f"player: {p['player'] or '（なし）'}")
        self.set_status("譜面数を数えています…")
        try:
            kept, checked, gone_leaf, gone_dir = prune_empty(
                folders, counter,
                progress=lambda n: self.set_status(f"譜面数を数えています… {n}/{total}"))
            folders[:] = kept
            msg = f"  {checked}件を確認し、0件だった {gone_leaf}件を除きました"
            if gone_dir:
                msg += f"（中身が無くなった親フォルダ {gone_dir}件も削除）"
            self.log(msg + f"（{time.time() - started:.1f}秒）")
        except Exception as e:  # noqa: BLE001
            self.log(f"  数え上げに失敗しました（{e}）。0件のフォルダもそのまま作ります。")
        finally:
            counter.close()

    def _log_leaves(self, nodes, limit):
        """作られる中身を数件だけログに出す。"""
        for node in nodes[:limit]:
            if node.get("folder") is not None:
                names = "、".join(c["name"] for c in node["folder"][:5])
                more = "…" if len(node["folder"]) > 5 else ""
                self.log(f"    {node['name']} / "
                         f"（{len(node['folder'])}件: {names}{more}）")
                continue
            sql = node.get("sql", "")
            if len(sql) > 68:
                sql = sql[:68] + "…"
            self.log(f"    {node['name']}: {sql}")
        if len(nodes) > limit:
            self.log(f"    …ほか {len(nodes) - limit}件")


def report_crash(text: str) -> Path | None:
    """
    起動できなかったときの内容をファイルに書き出す。
    exe（--windowed）では画面に何も出ないため、これが唯一の手がかりになる。
    """
    for base in (app_dir(), Path(os.environ.get("LOCALAPPDATA") or Path.home())):
        try:
            path = Path(base) / "beatoraja_folder_maker_error.log"
            stamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            with path.open("a", encoding="utf-8") as f:
                f.write(f"\n===== {stamp} =====\n")
                f.write(f"python: {sys.version}\n")
                f.write(f"exe: {getattr(sys, 'frozen', False)} / {sys.executable}\n")
                f.write(text)
            return path
        except Exception:  # noqa: BLE001
            continue
    return None


def main():
    app = App()
    app.mainloop()


if __name__ == "__main__":
    try:
        main()
    except Exception:  # noqa: BLE001
        tb = traceback.format_exc()
        traceback.print_exc()
        log = report_crash(tb)
        try:
            root = tk.Tk()
            root.withdraw()
            messagebox.showerror(
                APP_TITLE,
                "起動できませんでした。\n\n" + tb.strip().splitlines()[-1]
                + (f"\n\n詳しい内容: {log}" if log else ""))
            root.destroy()
        except Exception:  # noqa: BLE001
            pass
        sys.exit(1)
