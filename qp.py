#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
qp - 追问树 (inquiry tree)

记录"我为什么会产生这个疑问"的思考链路。设计原则：

1. 状态与渲染彻底分离。结构只存在于 .qp/trees.json 里，一个文件一棵树。
2. 结构字段最小化：每个节点只需 id 和 parent 就能完整复原整棵树。
   其余字段（raw / q / blocker / resolution / status / pos）都是内容，删掉不影响结构。
   pos 只是手工拖动的落点，删掉就回到自动布局。
3. 所有写操作走同一组 op_* 函数，CLI 和 Web UI 共用，行为必然一致。

用法见 `qp help`。
"""

import argparse
import atexit
import hashlib
import json
import os
import random
import shutil
import string
import subprocess
import sys
import threading
import time
import webbrowser
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs
import urllib.request
import urllib.error

DIRNAME = ".qp"
STORE = "trees.json"
SNAPSHOT = "index.html"
IMGDIR = "img"
VERSION = 1
ALPHABET = string.digits + string.ascii_lowercase
STOCK_TITLE = "qp - 追问树"

# --------------------------------------------------------------------------
# 前端资产：和 qp.py 放在同一个目录里
# --------------------------------------------------------------------------

UI_HTML = "qp-ui.html"
HOME_HTML = "qp-home.html"

# 页面模板与 Python 之间只有这四个约定，少一个就会静默失效，所以启动时先查一遍。
UI_MARKERS = ("/*__QP_DATA__*/null", "/*__QP_MD__*/null",
              "/*__QP_TITLE__*/qp - 追问树", "/*__QP_HOME__*/false")

_ASSETS = {}


def asset_path(name):
    # 必须 realpath：/opt/homebrew/bin/qp 是指向 qp.py 的软链，
    # 用 abspath 会把资产目录指到 /opt/homebrew/bin 去。
    return os.path.join(os.path.dirname(os.path.realpath(__file__)), name)


def _asset(name):
    if name not in _ASSETS:
        path = asset_path(name)
        try:
            with open(path, "r", encoding="utf-8") as f:
                _ASSETS[name] = f.read()
        except IOError as e:
            die("读不到 %s（它必须和 qp.py 放在同一个目录）：%s" % (path, e))
    return _ASSETS[name]


def require_assets():
    """启动时把两个模板读进来并核对占位符，缺东西立刻报错，别拖到打开页面才发现。"""
    ui = _asset(UI_HTML)
    missing = [m for m in UI_MARKERS if m not in ui]
    if missing:
        die("%s 里少了占位符：%s" % (asset_path(UI_HTML), "  ".join(missing)))
    _asset(HOME_HTML)


# Web 端是 ThreadingHTTPServer，双击之类的动作会并发打进来。
# 用一把锁把「改数据 + 写快照 + 取响应」串起来，避免读到写了一半的状态。
OP_LOCK = threading.Lock()


# --------------------------------------------------------------------------
# 基础工具
# --------------------------------------------------------------------------

def now():
    return datetime.now().strftime("%Y-%m-%d %H:%M")


def make_id(existing):
    while True:
        nid = "n" + "".join(random.choice(ALPHABET) for _ in range(4))
        if nid not in existing:
            return nid


class QPError(Exception):
    """可预期的用户错误。CLI 打印成一行，Web 端回成 JSON error。"""


def die(msg, code=1):
    # 统一抛异常而不是 sys.exit，这样 Web 端也能拿到具体原因。
    raise QPError(msg)


# --------------------------------------------------------------------------
# 存储
# --------------------------------------------------------------------------

class Store(object):
    """一个目录一个存储。root 是 .qp 目录。

    snapshot=True 时，每次 save 顺手把 .qp/index.html 静态快照也刷一遍 —— 命令行走这条。
    常驻的 Web 服务用 False，它在 OP_LOCK 里自己调 write_snapshot，免得同一份快照写两遍。
    """

    def __init__(self, root, snapshot=False):
        self.root = root
        self.file = os.path.join(root, STORE)
        self.data = self._load()
        self.snapshot = snapshot
        self._lock = threading.Lock()

    def _load(self):
        if not os.path.exists(self.file):
            return {"version": VERSION, "focus": None, "trees": [], "notes": []}
        try:
            with open(self.file, "r", encoding="utf-8") as f:
                data = json.load(f)
        except (ValueError, IOError) as e:
            die("无法读取 %s：%s" % (self.file, e))
        # 老文件没有 notes；补上空列表，省得每个读的地方都判一次
        if not isinstance(data.get("notes"), list):
            data["notes"] = []
        return data

    def save(self):
        """原子写，避免中途崩溃留下半个文件。

        临时名带上 pid，两个进程（比如 CLI 和正在跑的 ui）同时写也不会互相踩掉；
        进程内再用锁串行化，避免 os.replace 抢跑报错。
        """
        tmp = "%s.%d.tmp" % (self.file, os.getpid())
        with self._lock:
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.data, f, ensure_ascii=False, indent=2)
                f.write("\n")
            os.replace(tmp, self.file)
        if self.snapshot:
            write_snapshot(self)


def store_at(path, create, snapshot=False):
    root = os.path.join(path, DIRNAME)
    if not os.path.isdir(root):
        if not create:
            die("当前目录还没有 %s，先跑 `qp init`" % DIRNAME)
        os.makedirs(root, exist_ok=True)
    return Store(root, snapshot)


def cwd_store(create=False):
    """命令行每次改完数据都顺手刷新快照，跟 Web 端保持一致。"""
    return store_at(os.getcwd(), create, snapshot=True)


# --------------------------------------------------------------------------
# 图片：单独落盘，绝不塞进 trees.json
# --------------------------------------------------------------------------

IMG_MAGIC = ((b"\x89PNG", ".png"), (b"\xff\xd8\xff", ".jpg"),
             (b"GIF8", ".gif"), (b"RIFF", ".webp"), (b"BM", ".bmp"))

IMG_CTYPE = {".png": "image/png", ".jpg": "image/jpeg", ".jpeg": "image/jpeg",
             ".gif": "image/gif", ".webp": "image/webp", ".bmp": "image/bmp"}


def img_dir(store):
    d = os.path.join(store.root, IMGDIR)
    if not os.path.isdir(d):
        os.makedirs(d, exist_ok=True)
    return d


def save_image(store, blob):
    """按内容哈希落盘：同一张图重复粘贴也只存一份。返回文件名。"""
    ext = ".png"
    for magic, e in IMG_MAGIC:
        if blob.startswith(magic):
            ext = e
            break
    name = hashlib.sha1(blob).hexdigest()[:16] + ext
    path = os.path.join(img_dir(store), name)
    if not os.path.exists(path):
        tmp = "%s.%d.tmp" % (path, os.getpid())
        with open(tmp, "wb") as f:
            f.write(blob)
        os.replace(tmp, path)
    return name


# --------------------------------------------------------------------------
# 查找
# --------------------------------------------------------------------------

def all_nodes(data):
    for t in data["trees"]:
        for n in t["nodes"]:
            yield t, n


def find_node(data, nid):
    for t, n in all_nodes(data):
        if n["id"] == nid:
            return t, n
    return None, None


def resolve_id(data, token):
    """支持完整 id、唯一前缀、以及 @ / . / focus 表示当前焦点。"""
    if token in ("@", ".", "focus"):
        fid = data.get("focus")
        if not fid:
            die("还没有焦点节点")
        return fid
    ids = [n["id"] for _, n in all_nodes(data)]
    if token in ids:
        return token
    hits = [i for i in ids if i.startswith(token)]
    if len(hits) == 1:
        return hits[0]
    if not hits:
        die("找不到节点 %r" % token)
    die("%r 有歧义：%s" % (token, " ".join(sorted(hits))))


def tree_of(data, nid):
    t, _ = find_node(data, nid)
    return t


def path_to(data, nid):
    """返回从根到 nid 的节点列表（含两端）。"""
    t, n = find_node(data, nid)
    if not n:
        return []
    by_id = dict((x["id"], x) for x in t["nodes"])
    chain = []
    cur = n
    guard = 0
    while cur is not None and guard < 10000:
        chain.append(cur)
        p = cur.get("parent")
        cur = by_id.get(p) if p else None
        guard += 1
    chain.reverse()
    return chain


def children_of(tree, nid):
    return [n for n in tree["nodes"] if n.get("parent") == nid]


def roots_of(tree):
    return [n for n in tree["nodes"] if not n.get("parent")]


# --------------------------------------------------------------------------
# 所有写操作（CLI 与 Web UI 共用这一组）
# --------------------------------------------------------------------------

def op_new_tree(store, raw, source=""):
    if not (raw or "").strip():
        die("根节点不能为空")
    data = store.data
    ids = set(n["id"] for _, n in all_nodes(data))
    nid = make_id(ids)
    tree = {
        "id": "t" + nid[1:],
        "source": source or "",
        "nodes": [{
            "id": nid, "parent": None, "raw": raw, "q": "",
            "blocker": "", "resolution": "", "status": "open",
            "created": now(),
        }],
    }
    data["trees"].append(tree)
    data["focus"] = nid
    store.save()
    return nid


def op_add(store, parent_id, raw):
    if not (raw or "").strip():
        die("子问题不能为空")
    data = store.data
    tree = tree_of(data, parent_id)
    if tree is None:
        die("找不到父节点 %r" % parent_id)
    ids = set(n["id"] for _, n in all_nodes(data))
    nid = make_id(ids)
    tree["nodes"].append({
        "id": nid, "parent": parent_id, "raw": raw, "q": "",
        "blocker": "", "resolution": "", "status": "open",
        "created": now(),
    })
    data["focus"] = nid
    store.save()
    return nid


def op_edit(store, nid, raw, q=None):
    _, node = find_node(store.data, nid)
    if node is None:
        die("找不到节点 %r" % nid)
    node["raw"] = raw
    if q is not None:
        node["q"] = q
    store.save()
    return nid


def op_close(store, nid, blocker, resolution):
    _, node = find_node(store.data, nid)
    if node is None:
        die("找不到节点 %r" % nid)
    node["blocker"] = blocker or ""
    node["resolution"] = resolution or ""
    node["status"] = "closed"
    store.save()
    return nid


def op_reopen(store, nid):
    _, node = find_node(store.data, nid)
    if node is None:
        die("找不到节点 %r" % nid)
    node["status"] = "open"
    store.save()
    return nid


def op_delete(store, nid):
    """删除节点及其整棵子树。"""
    data = store.data
    tree = tree_of(data, nid)
    if tree is None:
        die("找不到节点 %r" % nid)
    doomed = set()
    frontier = [nid]
    while frontier:
        cur = frontier.pop()
        if cur in doomed:
            continue
        doomed.add(cur)
        frontier.extend(c["id"] for c in children_of(tree, cur))
    parent = None
    for n in tree["nodes"]:
        if n["id"] == nid:
            parent = n.get("parent")
    tree["nodes"] = [n for n in tree["nodes"] if n["id"] not in doomed]
    if not tree["nodes"]:
        data["trees"] = [t for t in data["trees"] if t["id"] != tree["id"]]
    if data.get("focus") in doomed:
        nxt = parent
        if nxt is None and data["trees"]:
            nxt = roots_of(data["trees"][0])[0]["id"]
        data["focus"] = nxt
    store.save()
    return sorted(doomed)


def op_focus(store, nid):
    if nid is not None and find_node(store.data, nid)[1] is None:
        die("找不到节点 %r" % nid)
    store.data["focus"] = nid
    store.save()
    return nid


CONTENT_KEYS = ("raw", "q", "blocker", "resolution", "status")


def op_set_fields(store, nid, fields):
    """按字段改内容。界面里原地编辑的字段都走这里。"""
    _, node = find_node(store.data, nid)
    if node is None:
        die("找不到节点 %r" % nid)
    for k in CONTENT_KEYS:
        if k in fields and fields[k] is not None:
            node[k] = fields[k]
    store.save()
    return nid


def op_set_source(store, tree_id, source):
    for t in store.data["trees"]:
        if t["id"] == tree_id:
            t["source"] = source or ""
            store.save()
            return tree_id
    die("找不到树 %r" % tree_id)


def op_set_pos(store, nid, pos):
    """记下手工拖动后的坐标（画布像素）。pos 为 None 表示清掉、回到自动布局。"""
    _, node = find_node(store.data, nid)
    if node is None:
        die("找不到节点 %r" % nid)
    if pos is None:
        node.pop("pos", None)
    else:
        node["pos"] = [round(float(pos[0])), round(float(pos[1]))]
    store.save()
    return nid


def op_reset_pos(store, nid=None):
    """清掉手工坐标。给 id 只清这一个，否则清当前焦点所在的整棵树。"""
    if nid:
        _, node = find_node(store.data, nid)
        if node is None:
            die("找不到节点 %r" % nid)
        targets = [node]
    else:
        tree = tree_of(store.data, store.data.get("focus"))
        if tree is None and store.data["trees"]:
            tree = store.data["trees"][0]
        targets = tree["nodes"] if tree else []
    n = 0
    for x in targets:
        if "pos" in x:
            x.pop("pos")
            n += 1
    store.save()
    return n


def op_reset_tree(store, tree_id=None):
    """一键归位：把一整棵树里所有手工坐标清掉，全部回到自动布局。"""
    if tree_id:
        tree = tree_by_token(store.data, tree_id)
    else:
        tree = tree_of(store.data, store.data.get("focus"))
        if tree is None and store.data["trees"]:
            tree = store.data["trees"][0]
    n = 0
    for x in (tree["nodes"] if tree else []):
        if "pos" in x:
            x.pop("pos")
            n += 1
    if n:
        store.save()
    return n


def op_add_img(store, nid, name):
    """把一张已经落盘的图片挂到节点上。"""
    _, node = find_node(store.data, nid)
    if node is None:
        die("找不到节点 %r" % nid)
    imgs = node.setdefault("imgs", [])
    if name not in imgs:
        imgs.append(name)
    store.save()
    return name


def op_del_img(store, nid, name):
    _, node = find_node(store.data, nid)
    if node is None:
        die("找不到节点 %r" % nid)
    if name in (node.get("imgs") or []):
        node["imgs"].remove(name)
        if not node["imgs"]:
            node.pop("imgs", None)
    store.save()
    return name


def op_add_img_node(store, name, parent=None, pos=None):
    """粘贴图片时新建的「图片节点」。

    它就是普通节点，只是 kind="img" —— 所以连线、拖动、删除整棵子树这些逻辑
    一行都不用改。刚插进来时 parent 是空的（自由节点），等用户点一个节点把它接上去。
    """
    data = store.data
    if parent:
        tree = tree_of(data, parent)
        if tree is None:
            die("找不到父节点 %r" % parent)
    else:
        tree = tree_of(data, data.get("focus"))
        if tree is None and data["trees"]:
            tree = data["trees"][0]
        if tree is None:
            die("先建一棵树，图片才有地方放")
    ids = set(n["id"] for _, n in all_nodes(data))
    nid = make_id(ids)
    node = {"id": nid, "parent": parent, "kind": "img", "imgs": [name],
            "raw": "", "q": "", "blocker": "", "resolution": "",
            "status": "open", "created": now()}
    if pos:
        node["pos"] = [round(float(pos[0])), round(float(pos[1]))]
    tree["nodes"].append(node)
    data["focus"] = nid
    store.save()
    return nid


def op_set_parent(store, nid, parent=None):
    """换父节点。「把这张图连到谁」就走这里，parent=None 表示断开成自由节点。"""
    data = store.data
    tree = tree_of(data, nid)
    if tree is None:
        die("找不到节点 %r" % nid)
    if parent is not None:
        if parent == nid:
            die("不能连到自己")
        ptree = tree_of(data, parent)
        if ptree is None:
            die("找不到父节点 %r" % parent)
        if ptree is not tree:
            die("只能连到同一棵树里的节点")
        cur, guard = parent, 0
        while cur and guard < 10000:          # 顺着往上走，走回自己就成了环
            if cur == nid:
                die("连上去会绕成一个环")
            _, pn = find_node(data, cur)
            cur = (pn or {}).get("parent")
            guard += 1
    _, node = find_node(data, nid)
    node["parent"] = parent
    store.save()
    return nid


# --------------------------------------------------------------------------
# 笔记：和「树」并列的一种文档 —— 长文 markdown，不塞进树里
# --------------------------------------------------------------------------

def note_id(existing):
    while True:
        nid = "p" + "".join(random.choice(ALPHABET) for _ in range(4))
        if nid not in existing:
            return nid


def find_note(data, nid):
    for p in data.get("notes") or []:
        if p["id"] == nid:
            return p
    return None


def op_new_note(store, title="", md=""):
    notes = store.data.setdefault("notes", [])
    nid = note_id(set(p["id"] for p in notes))
    notes.append({"id": nid, "title": (title or "").strip() or "未命名笔记",
                  "md": md or "", "created": now(), "updated": now()})
    store.save()
    return nid


def op_set_note(store, nid, title=None, md=None):
    p = find_note(store.data, nid)
    if p is None:
        die("找不到笔记 %r" % nid)
    if title is not None:
        p["title"] = title.strip() or "未命名笔记"
    if md is not None:
        p["md"] = md
    p["updated"] = now()
    store.save()
    return nid


def op_del_note(store, nid):
    data = store.data
    if find_note(data, nid) is None:
        die("找不到笔记 %r" % nid)
    data["notes"] = [p for p in (data.get("notes") or []) if p["id"] != nid]
    store.save()
    return nid


def apply_op(store, req):
    """Web UI 的统一入口。"""
    op = req.get("op")
    if op == "new_tree":
        return op_new_tree(store, req.get("raw", ""), req.get("source", ""))
    if op == "add":
        return op_add(store, req["parent"], req.get("raw", ""))
    if op == "edit":
        return op_edit(store, req["id"], req.get("raw", ""), req.get("q"))
    if op == "close":
        return op_close(store, req["id"], req.get("blocker", ""), req.get("resolution", ""))
    if op == "reopen":
        return op_reopen(store, req["id"])
    if op == "delete":
        return op_delete(store, req["id"])
    if op == "focus":
        return op_focus(store, req.get("id"))
    if op == "set_fields":
        return op_set_fields(store, req["id"], req.get("fields") or {})
    if op == "set_source":
        return op_set_source(store, req["tree"], req.get("source", ""))
    if op == "set_pos":
        return op_set_pos(store, req["id"], req.get("pos"))
    if op == "reset_pos":
        return op_reset_pos(store, req.get("id"))
    if op == "reset_layout":
        return op_reset_tree(store, req.get("tree"))
    if op == "del_img":
        return op_del_img(store, req["id"], req["name"])
    if op == "add_img_node":
        return op_add_img_node(store, req["name"], req.get("parent"), req.get("pos"))
    if op == "set_parent":
        return op_set_parent(store, req["id"], req.get("parent"))
    if op == "new_note":
        return op_new_note(store, req.get("title", ""), req.get("md", ""))
    if op == "set_note":
        return op_set_note(store, req["id"], req.get("title"), req.get("md"))
    if op == "del_note":
        return op_del_note(store, req["id"])
    raise ValueError("未知操作 %r" % op)


# --------------------------------------------------------------------------
# 文本渲染（可追踪、可 diff 的输出）
# --------------------------------------------------------------------------

def label(node):
    text = node.get("q") or node.get("raw")
    if text:
        return text
    return "（图片）" if node.get("kind") == "img" else "(空)"


def ascii_tree(tree, with_ids=False):
    out = []
    by_parent = {}
    for n in tree["nodes"]:
        by_parent.setdefault(n.get("parent"), []).append(n)

    head = ""
    if with_ids:
        head = "tree %s" % tree["id"]
        if tree.get("source"):
            head += "  源: " + tree["source"]
    elif tree.get("source"):
        head = "源: " + tree["source"]
    if head:
        out.append(head)

    def walk(parent, prefix):
        kids = by_parent.get(parent, [])
        for i, n in enumerate(kids):
            last = (i == len(kids) - 1)
            line = prefix + ("└─ " if last else "├─ ") + label(n)
            if n.get("status") == "closed":
                line += "  ✓"
            if n.get("imgs"):
                line += "  [图×%d]" % len(n["imgs"])
            if with_ids:
                line += "  " + n["id"]
            out.append(line)
            kid_prefix = prefix + ("   " if last else "│  ")
            for extra_key, extra_tag in (("blocker", "卡点"), ("resolution", "已明白")):
                val = n.get(extra_key)
                if val:
                    out.append(kid_prefix + "· %s: %s" % (extra_tag, val))
            walk(n["id"], kid_prefix)

    walk(None, "")
    return "\n".join(out)


def _flat(s):
    return (s or "").replace("\r", " ").replace("\n", " ").strip()


def tree_markdown(tree):
    """一棵树导成 markdown：根做标题，往下一层层嵌套列表，卡点/已明白挂在节点下。"""
    by_parent = {}
    for n in tree["nodes"]:
        by_parent.setdefault(n.get("parent"), []).append(n)

    out = []

    def notes(node, depth):
        pad = "  " * (depth + 1)
        for key, tag in (("blocker", "卡点"), ("resolution", "已明白")):
            if node.get(key):
                out.append(pad + "- " + tag + "：" + _flat(node[key]))

    def walk(parent, depth):
        for n in by_parent.get(parent, []):
            pad = "  " * depth
            imgs = n.get("imgs") or []
            if n.get("kind") == "img":
                # 图片节点：图本身就是这一条，描述当 alt
                cap = _flat(n.get("raw") or "")
                if imgs:
                    out.append(pad + "- ![" + cap + "](%s/%s/%s)" % (DIRNAME, IMGDIR, imgs[0]))
                else:
                    out.append(pad + "- " + (cap or "（图片）"))
                notes(n, depth)
                walk(n["id"], depth + 1)
                continue
            mark = " ✓" if n.get("status") == "closed" else ""
            out.append(pad + "- " + _flat(label(n)) + mark)
            notes(n, depth)
            for name in imgs:
                out.append("  " * (depth + 1) + "- ![](%s/%s/%s)" % (DIRNAME, IMGDIR, name))
            walk(n["id"], depth + 1)

    for i, root in enumerate(by_parent.get(None, [])):
        if i:
            out.append("")
        out.append("# " + _flat(label(root)))
        meta = ["来源：" + tree["source"]] if tree.get("source") else []
        for key, tag in (("blocker", "卡点"), ("resolution", "已明白")):
            if root.get(key):
                meta.append(tag + "：" + _flat(root[key]))
        if meta:
            out.append("")
            out.extend(meta)
        for name in root.get("imgs") or []:
            # 自由图片节点自己就是根，这时图要带上它的描述
            cap = _flat(root.get("raw") or "") if root.get("kind") == "img" else ""
            out.append("")
            out.append("![%s](%s/%s/%s)" % (cap, DIRNAME, IMGDIR, name))
        out.append("")
        walk(root["id"], 0)

    return "\n".join(out).rstrip() + "\n"


def note_markdown(note):
    out = ["# " + _flat(note.get("title") or "未命名笔记"), ""]
    body = (note.get("md") or "").rstrip()
    if body:
        out.append(body)
    return "\n".join(out).rstrip() + "\n"


def doc_markdown(data, tree_id=None):
    """整份导出；给了 tree_id 就只导那一棵（此时不带笔记）。"""
    if tree_id:
        trees = [tree_by_token(data, tree_id)]
        notes = []
    else:
        trees = data["trees"]
        notes = data.get("notes") or []
    if not trees and not notes:
        die("还没有树或笔记")
    parts = [tree_markdown(t) for t in trees] + [note_markdown(p) for p in notes]
    return "\n---\n\n".join(parts)


# --------------------------------------------------------------------------
# LLM（可选，用于 close 起草与界面里的对话）
# --------------------------------------------------------------------------

# 内置几家 OpenAI 兼容的服务。config.json 里写 {"preset": "siliconflow", "api_key": "sk-xxx"}
# 就够了；要换模型再补 "model"。免费额度和模型名会变，配完跑一次 `qp llm --test` 验一下。
#
# "params" 会原样并进请求体，用来关各家自己的开关。最要紧的一个是**思维链**：
#   Qwen3 / GLM-4.5+ 这些默认开思考，简单的一句话也会憋十几秒才吐第一个字
#   （实测 Qwen3-8B：首字 14.5s → 0.66s，就差这个开关）。
# 想让它思考，就在自己的 config.json 里写 "params": {} 或把值改回去覆盖掉。
PRESETS = {
    "siliconflow": {
        "endpoint": "https://api.siliconflow.cn/v1",
        "model": "Qwen/Qwen3-8B",
        "params": {"enable_thinking": False},
        "note": "国内直连，9B 以下永久免费；关思考后首字 ~0.6s",
    },
    "zhipu": {
        "endpoint": "https://open.bigmodel.cn/api/paas/v4",
        "model": "glm-4.7-flash",
        "params": {"thinking": {"type": "disabled"}},
        "note": "智谱 GLM-4.7-Flash 免费，中文好；高峰期容易 429",
    },
    "dashscope": {
        "endpoint": "https://dashscope.aliyuncs.com/compatible-mode/v1",
        "model": "qwen-flash",
        "params": {"enable_thinking": False},
        "note": "阿里云百炼，新用户各模型送 100 万 token（90 天）",
    },
    "modelscope": {
        "endpoint": "https://api-inference.modelscope.cn/v1",
        "model": "Qwen/Qwen3-8B",
        "params": {"enable_thinking": False},
        "note": "魔搭，每天 2000 次免费",
    },
    "groq": {
        "endpoint": "https://api.groq.com/openai/v1",
        "model": "openai/gpt-oss-20b",
        "note": "国外，LPU 极快（数百 tok/s），国内要代理",
    },
}

GLOBAL_CFG = os.path.join(os.path.expanduser("~"), ".qp", "config.json")

LLM_HELP = (
    "还没配置模型。最省事的一条：\n"
    "  qp llm --preset zhipu --key sk-xxx --global\n"
    "看有哪些预设：qp llm --list\n"
    "不加 --global 就只配当前项目；加了就写进 " + GLOBAL_CFG + "，所有项目共用。\n"
    "也可以手写 JSON（{\"preset\":\"...\",\"api_key\":\"...\"}），\n"
    "或设环境变量 QP_ENDPOINT / QP_API_KEY / QP_MODEL。"
)


def cfg_path(root):
    return os.path.join(root, "config.json")


def read_cfg_file(p):
    if not p or not os.path.exists(p):
        return {}
    try:
        with open(p, "r", encoding="utf-8") as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except (ValueError, IOError):
        return {}


def save_cfg(root, cfg):
    return save_cfg_file(cfg_path(root), cfg)


def save_cfg_file(p, cfg):
    d = os.path.dirname(p)
    if d and not os.path.isdir(d):
        os.makedirs(d)
    tmp = p + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(cfg, f, ensure_ascii=False, indent=2)
    os.replace(tmp, p)
    return p


def load_cfg(root):
    """优先级：环境变量 > 项目里的 .qp/config.json > 全局 ~/.qp/config.json > 预设。

    全局那份是给「好多项目共用一个 key」用的 —— 配一次，到处都能聊。
    cfg_sources() 顺带记下每台来源，`qp llm` 会打出来，免得配了半天不知道在读哪个文件。
    "params" 是按 key 合并的（不是整块替换），所以想单独把某个开关改回去很容易。
    """
    cfg = {"preset": "", "endpoint": "", "api_key": "", "model": "", "params": {}}
    for p in (GLOBAL_CFG, cfg_path(root)):
        for k, v in read_cfg_file(p).items():
            if k == "params":
                if isinstance(v, dict):
                    cfg["params"].update(v)
            elif v or k not in cfg:
                cfg[k] = v
    preset = PRESETS.get((cfg.get("preset") or "").strip()) or {}
    for k in ("endpoint", "model"):          # 预设只兜底，不覆盖显式写的字段
        if not cfg.get(k):
            cfg[k] = preset.get(k) or ""
    for k, v in (preset.get("params") or {}).items():
        cfg["params"].setdefault(k, v)
    for k, env in (("endpoint", "QP_ENDPOINT"), ("api_key", "QP_API_KEY"), ("model", "QP_MODEL")):
        if os.environ.get(env):
            cfg[k] = os.environ[env]
    return cfg


def cfg_sources(root):
    """实际读到的配置文件（去重：在 ~ 下跑时全局那份就是项目那份）。"""
    out, seen = [], set()
    for p in (GLOBAL_CFG, cfg_path(root)):
        if not os.path.exists(p):
            continue
        key = os.path.realpath(p)
        if key in seen:
            continue
        seen.add(key)
        out.append(p)
    return out


def _chat_url(endpoint):
    """允许只填基址（.../v1），也允许直接填完整的 .../chat/completions。"""
    u = (endpoint or "").strip().rstrip("/")
    if not u:
        return ""
    return u if u.endswith("/chat/completions") else u + "/chat/completions"


def _llm_open(cfg, payload, timeout):
    url = _chat_url(cfg.get("endpoint"))
    if not url or not cfg.get("api_key"):
        raise RuntimeError(LLM_HELP)
    req = urllib.request.Request(
        url, data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json",
                 "Authorization": "Bearer " + cfg["api_key"],
                 "Accept": "text/event-stream" if payload.get("stream") else "application/json"},
    )
    try:
        return urllib.request.urlopen(req, timeout=timeout)
    except urllib.error.HTTPError as e:
        detail = e.read().decode("utf-8", "replace")[:400]
        raise RuntimeError("模型返回 %s：%s" % (e.code, detail))
    except Exception as e:
        raise RuntimeError("连不上模型（%s）：%s" % (cfg.get("endpoint"), e))


def _llm_model(cfg):
    return cfg.get("model") or "Qwen/Qwen3-8B"


def _llm_payload(cfg, messages, stream, temperature):
    """统一在这里拼请求体。cfg["params"] 最后并进来，用来关各家的思维链之类
    （那玩意儿让首字从 0.6s 变成 14s，对「梳理一下」是纯负担）。"""
    payload = {"model": _llm_model(cfg), "messages": messages,
               "temperature": temperature, "stream": stream}
    for k, v in (cfg.get("params") or {}).items():
        if k not in ("model", "messages", "stream"):     # 这几个别让 params 改掉
            payload[k] = v
    return payload


def llm_chat(cfg, prompt, timeout=60, temperature=0.2):
    """prompt 可以是一句话，也可以是一整个 messages 列表（多轮）。"""
    msgs = prompt if isinstance(prompt, list) else [{"role": "user", "content": prompt}]
    payload = _llm_payload(cfg, msgs, False, temperature)
    with _llm_open(cfg, payload, timeout) as r:
        data = json.loads(r.read().decode("utf-8"))
    try:
        return data["choices"][0]["message"]["content"].strip()
    except (KeyError, IndexError):
        raise RuntimeError("模型返回格式看不懂：%s" % json.dumps(data, ensure_ascii=False)[:400])


def llm_stream(cfg, messages, timeout=120, temperature=0.3):
    """逐段 yield 文本增量。有的服务忽略 stream 参数、直接回完整 JSON，这时退回一次性给全文。"""
    payload = _llm_payload(cfg, messages, True, temperature)
    r = _llm_open(cfg, payload, timeout)
    got = False
    try:
        for raw in r:
            line = raw.decode("utf-8", "replace").strip()
            if not line.startswith("data:"):
                continue
            chunk = line[5:].strip()
            if chunk == "[DONE]":
                break
            try:
                obj = json.loads(chunk)
                piece = obj["choices"][0]["delta"].get("content") or ""
            except (ValueError, KeyError, IndexError, AttributeError):
                piece = ""
            if piece:
                got = True
                yield piece
    finally:
        r.close()
    if not got:
        yield llm_chat(cfg, messages, timeout=timeout, temperature=temperature)


PROMPT_CLOSE = (
    "一个人在读论文时，从父节点产生了一个子问题，并沿着这条分支追问下去。\n\n"
    "父节点：%s\n\n这条分支上的节点：\n%s\n\n"
    "请输出两行，不要其他内容：\n"
    "卡点：<父节点里哪个说法/词没有被理解，才逼出了这个子问题>\n"
    "已明白：<一句话总结这条分支解决了什么>\n"
)


# --------------------------------------------------------------------------
# Web UI
# --------------------------------------------------------------------------



def _js_json(obj):
    return json.dumps(obj, ensure_ascii=False).replace("<", "\\u003c")


def _esc_html(s):
    return (s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))


def _fill_html(data, md, title, home):
    return (_asset(UI_HTML).replace("/*__QP_DATA__*/null", _js_json(data) if data is not None else "null")
                .replace("/*__QP_MD__*/null", _js_json(md) if md is not None else "null")
                .replace("/*__QP_TITLE__*/qp - 追问树", _esc_html(title or STOCK_TITLE))
                .replace("/*__QP_HOME__*/false", _js_json(home) if home else "false"))


def html_snapshot(data):
    """只读快照：数据和 markdown 都内嵌，所以没服务也能看、也能导出。"""
    md = dict((t["id"], tree_markdown(t)) for t in data["trees"])
    return _fill_html(data, md, None, "")


def html_live(title=None, home=""):
    return _fill_html(None, None, title, home)


def write_snapshot(store):
    p = os.path.join(store.root, SNAPSHOT)
    with open(p, "w", encoding="utf-8") as f:
        f.write(html_snapshot(store.data))
    return p


# 只读快照有 30–45KB（模板 + 内嵌数据 + 每棵树的 markdown）。点一下气泡就重写一遍太浪费，
# 所以界面里改成「离手之后再写」：每次改动只重排一次定时器，停手 2 秒后才真正落盘；
# 退出/关窗时再冲刷一次，保证快照不会停在上一次的位置。
SNAPSHOT_DELAY = 2.0
_SNAP_LOCK = threading.Lock()
_SNAP_TIMERS = {}          # store.file -> [timer, store]


def schedule_snapshot(store):
    with _SNAP_LOCK:
        old = _SNAP_TIMERS.get(store.file)
        if old:
            old[0].cancel()
        t = threading.Timer(SNAPSHOT_DELAY, flush_snapshot, args=(store,))
        t.daemon = True
        _SNAP_TIMERS[store.file] = [t, store]
    t.start()


def flush_snapshot(store):
    with _SNAP_LOCK:
        cur = _SNAP_TIMERS.pop(store.file, None)
    if cur:
        cur[0].cancel()
    try:
        write_snapshot(store)
    except OSError:
        pass            # 快照只是顺手产物，写不动不该影响正在做的事


def flush_all_snapshots():
    with _SNAP_LOCK:
        stores = [v[1] for v in _SNAP_TIMERS.values()]
    for st in stores:
        flush_snapshot(st)


atexit.register(flush_all_snapshots)


class Handler(BaseHTTPRequestHandler):
    store = None
    title = None
    home_url = ""

    def _send(self, code, ctype, body):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _json(self, obj, code=200):
        self._send(code, "application/json; charset=utf-8",
                   json.dumps(obj, ensure_ascii=False).encode("utf-8"))

    def _send_img(self, name):
        # 只认 basename，挡掉 ../ 这类穿越
        name = os.path.basename(name or "")
        path = os.path.join(self.store.root, IMGDIR, name)
        if not (name and os.path.isfile(path)):
            self._send(404, "text/plain; charset=utf-8", b"not found")
            return
        ext = os.path.splitext(name)[1].lower()
        with open(path, "rb") as f:
            blob = f.read()
        self._send(200, IMG_CTYPE.get(ext, "application/octet-stream"), blob)

    def do_GET(self):
        u = urlparse(self.path)
        p = u.path
        if p in ("/", "/index.html"):
            body = html_live(self.title, self.home_url).encode("utf-8")
            self._send(200, "text/html; charset=utf-8", body)
        elif p.startswith("/img/"):
            self._send_img(p[5:])
        elif p == "/api/state":
            with OP_LOCK:
                payload = json.dumps(self.store.data, ensure_ascii=False).encode("utf-8")
            self._send(200, "application/json; charset=utf-8", payload)
        elif p == "/api/md":
            tid = (parse_qs(u.query).get("tree") or [None])[0]
            try:
                with OP_LOCK:
                    text = doc_markdown(self.store.data, tid)
            except Exception as e:
                self._json({"error": str(e) or "导出失败"}, 400)
                return
            self._send(200, "text/markdown; charset=utf-8", text.encode("utf-8"))
        elif p == "/api/llm":
            # 只报告「配没配好 / 用的哪个模型」，不吐 key
            cfg = load_cfg(self.store.root)
            self._json({"configured": bool(cfg.get("endpoint") and cfg.get("api_key")),
                        "model": cfg.get("model") or "",
                        "endpoint": cfg.get("endpoint") or "",
                        "preset": cfg.get("preset") or ""})
        else:
            self._send(404, "text/plain; charset=utf-8", b"not found")

    def do_POST(self):
        p = urlparse(self.path).path
        if p == "/api/img":
            self._post_img()
            return
        try:
            n = int(self.headers.get("Content-Length") or 0)
            req = json.loads(self.rfile.read(n).decode("utf-8") or "{}")
        except (ValueError, TypeError):
            self._json({"error": "请求体不是合法 JSON"}, 400)
            return

        if p == "/api/chat":
            self._chat(req)
            return

        if p == "/api/op":
            try:
                with OP_LOCK:
                    apply_op(self.store, req)
                    schedule_snapshot(self.store)
                    payload = json.dumps(self.store.data, ensure_ascii=False).encode("utf-8")
            except Exception as e:
                self._json({"error": str(e) or "操作失败"}, 400)
                return
            self._send(200, "application/json; charset=utf-8", payload)
            return

        if p == "/api/llm":
            try:
                self._json(self._run_llm(req))
            except Exception as e:
                self._json({"error": str(e)}, 400)
            return

        self._json({"error": "not found"}, 404)

    def _post_img(self):
        """原始字节上传（不走 base64）。

        ?id=<节点>   挂到已有节点上（老用法）
        不给 id       新建一个自由的「图片节点」，落在 ?at=x,y 处（画布坐标，可选）
        ?parent=<节点> 新建时直接连到它（一般不用，连人是后面点出来的）
        """
        qs = parse_qs(urlparse(self.path).query)
        nid = (qs.get("id") or [""])[0]
        parent = (qs.get("parent") or [""])[0] or None
        at = (qs.get("at") or [""])[0]
        pos = None
        if at:
            try:
                a, b = at.split(",")[:2]
                pos = (float(a), float(b))
            except ValueError:
                pos = None
        try:
            n = int(self.headers.get("Content-Length") or 0)
        except ValueError:
            n = 0
        blob = self.rfile.read(n) if n > 0 else b""
        if not blob:
            self._json({"error": "空图片"}, 400)
            return
        try:
            with OP_LOCK:
                name = save_image(self.store, blob)
                if nid:
                    op_add_img(self.store, nid, name)
                else:
                    op_add_img_node(self.store, name, parent, pos)
                schedule_snapshot(self.store)
                payload = json.dumps(self.store.data, ensure_ascii=False).encode("utf-8")
        except Exception as e:
            self._json({"error": str(e) or "加入图片失败"}, 400)
            return
        self._send(200, "application/json; charset=utf-8", payload)

    def _run_llm(self, req):
        cfg = load_cfg(self.store.root)
        tree, node = find_node(self.store.data, req.get("id"))
        if node is None:
            raise RuntimeError("找不到节点")
        task = req.get("task")
        if task == "close":
            parent = None
            if node.get("parent"):
                parent = [x for x in tree["nodes"] if x["id"] == node["parent"]]
                parent = parent[0] if parent else None
            chain = path_to(self.store.data, node["id"])
            lines = []
            for i, x in enumerate(chain):
                lines.append("  " * i + "- " + (x.get("q") or x.get("raw", "")))
            out = llm_chat(cfg, PROMPT_CLOSE % (
                (parent.get("q") or parent.get("raw")) if parent else "（这是根节点）",
                "\n".join(lines),
            ))
            blocker, resolution = "", ""
            for ln in out.splitlines():
                ln = ln.strip()
                if ln.startswith("卡点"):
                    blocker = ln.split("：", 1)[-1].split(":", 1)[-1].strip()
                elif ln.startswith("已明白"):
                    resolution = ln.split("：", 1)[-1].split(":", 1)[-1].strip()
            if not blocker and not resolution:
                resolution = out
            return {"blocker": blocker, "resolution": resolution}
        raise RuntimeError("未知任务 %r" % task)

    def _chat(self, req):
        """流式对话。响应是 NDJSON：一行一个 {"d": "增量"}，最后一行 {"done": true}。

        不收整段对话、也不存服务端 —— 历史由前端拿着，每次原样带过来。
        这样 3 行代码就能多轮，还能顺手截断超长历史。
        """
        cfg = load_cfg(self.store.root)
        clean = []
        for m in (req.get("messages") or [])[-24:]:
            role = (m or {}).get("role")
            content = ((m or {}).get("content") or "").strip()
            if role in ("user", "assistant") and content:
                clean.append({"role": role, "content": content})
        if not clean:
            self._json({"error": "空的对话"}, 400)
            return

        self.send_response(200)
        self.send_header("Content-Type", "application/x-ndjson; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.end_headers()

        def emit(obj):
            self.wfile.write((json.dumps(obj, ensure_ascii=False) + "\n").encode("utf-8"))
            self.wfile.flush()

        # 前端按「停止」= 关连接 → 这里写回去会 BrokenPipe，顺手把上游也掐掉。
        # 不显式 close 的话，生成器要等 GC 才关，中间那段等于白烧免费额度。
        gen = llm_stream(cfg, clean)
        try:
            for piece in gen:
                emit({"d": piece})
            emit({"done": True})
        except (BrokenPipeError, ConnectionResetError):
            pass                     # 用户按了停止 / 关掉了页面，不算错
        except Exception as e:
            try:
                emit({"error": str(e)})
            except Exception:
                pass
        finally:
            try:
                gen.close()
            except Exception:
                pass

    def log_message(self, *a):
        pass


def make_handler(store, title=None, home_url=""):
    """每台服务一个独立的 Handler 子类 —— 否则多个项目会互踩类属性 store。"""
    return type("H", (Handler,), {"store": store, "title": title, "home_url": home_url})


def bind_server(port, handler):
    for candidate in range(port, port + 30):
        try:
            return ThreadingHTTPServer(("127.0.0.1", candidate), handler), candidate
        except OSError:
            continue
    die("端口 %d 起不来" % port)


def project_title(store):
    return "qp · " + os.path.basename(os.path.dirname(os.path.abspath(store.root)))


def start_project_server(store, port=8766, home_url=""):
    """返回 (httpd, url)。已经有人占着端口也无所谓，会自动往后找。"""
    write_snapshot(store)
    httpd, port = bind_server(port, make_handler(store, project_title(store), home_url))
    return httpd, "http://127.0.0.1:%d/" % port


CHROME = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"

WINDOW_TITLE = "qp"


class _NativeBridge:
    """原生窗口里的一点点 JS→Python：把导出的 markdown 真正写进「下载」文件夹。

    为什么非要走 Python：WKWebView 不认 blob 链接上的 `download` 属性，点了会把
    窗口直接导航成一页 markdown —— 应用界面被顶掉，文件其实也没落盘。写文件这步
    交给 Python 更稳，顺带能把真实路径回报给前端提示「存到哪了」。
    """

    def save_md(self, name, text):
        try:
            home = os.path.expanduser("~")
            base = os.path.join(home, "Downloads")
            if not os.path.isdir(base):
                base = home
            safe = os.path.basename(str(name or "qp.md")).strip() or "qp.md"
            stem, ext = os.path.splitext(safe)
            if not ext:
                ext = ".md"
            path = os.path.join(base, stem + ext)
            i = 2
            while os.path.exists(path):          # 重名就往后编号，不覆盖已有文件
                path = os.path.join(base, "%s %d%s" % (stem, i, ext))
                i += 1
            with open(path, "w", encoding="utf-8") as f:
                f.write(text or "")
            return path
        except Exception as e:
            return "ERR:" + str(e)


def run_native_window(url, title=WINDOW_TITLE):
    """用系统自带的 WKWebView（pywebview）开一个原生窗口，阻塞到窗口关闭。

    返回 True = 正常跑完了窗口生命周期；False = pywebview 用不了（没装 / 不在图形
    会话里），调用方该往后退到 Chrome 或默认浏览器。
    """
    try:
        import webview
    except Exception:
        return False
    try:
        # text_select 默认是 False —— 那样 pywebview 会往页面里塞一条
        # `body{user-select:none}`，整个应用一个字都选不中，没法复制。必须显式打开。
        kw = dict(width=1180, height=820, min_size=(720, 520), text_select=True)
        try:
            webview.create_window(title, url, js_api=_NativeBridge(), **kw)
        except TypeError:
            # 老版本 pywebview 不认 js_api：宁可不带桥，也别整个退化成浏览器
            webview.create_window(title, url, **kw)
        webview.start()
    except Exception:
        return False
    return True


def open_chrome_app(url):
    """退路：系统 Chrome 的 --app 模式，开一个没有地址栏的窗口。"""
    if os.path.exists(CHROME):
        subprocess.Popen([CHROME, "--app=" + url],
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        return True
    return False


def open_window(url, title=WINDOW_TITLE):
    """开窗口：原生窗口 > Chrome --app > 默认浏览器，返回用了哪个。"""
    if run_native_window(url, title):
        return "native"
    if open_chrome_app(url):
        return "chrome"
    webbrowser.open(url)
    return "browser"


_NO_PROXY = urllib.request.build_opener(urllib.request.ProxyHandler({}))


def server_alive(url):
    try:
        with _NO_PROXY.open(url + "api/ping", timeout=1) as r:
            return json.loads(r.read().decode("utf-8")).get("ok") == 1
    except Exception:
        return False


def serve(store, port, open_browser):
    httpd, url = start_project_server(store, port)
    port = httpd.server_address[1]
    print("qp ui  ->  " + url)
    print("存储   ->  " + store.file)
    print("快照   ->  " + os.path.join(store.root, SNAPSHOT))
    print("")
    print("提示：保持这个终端开着。关掉它服务就停了，浏览器那边会提示「连不上本地服务」。")
    print("      重跑 qp ui 就能接上，数据不会丢。  Ctrl-C 停止。")
    if open_browser:
        threading.Timer(0.4, lambda: webbrowser.open(url)).start()
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\n已停止。")
    finally:
        httpd.server_close()


# --------------------------------------------------------------------------
# qp home：项目管理器
# --------------------------------------------------------------------------


SKIP_NAMES = set((
    "node_modules", "__pycache__", "site-packages", "dist", "build", "target",
    "Library", "Applications", "Movies", "Music", "Pictures", "Public",
    "opt", "var", "tmp", "usr", "bin", "etc", "System", "Volumes",
))

_SCAN = {"t": 0.0, "data": None}
_SCAN_LOCK = threading.Lock()


def short_path(path):
    h = os.path.expanduser("~")
    if path == h:
        return "~"
    if path.startswith(h + os.sep):
        return "~" + path[len(h):]
    return path


def read_project(path):
    """读一个已经有 .qp 的目录，返回列表页要显示的那点信息。"""
    try:
        st = Store(os.path.join(path, DIRNAME))
        data = st.data
    except Exception:
        return None
    trees = data.get("trees") or []
    covers = []
    for t in trees[:2]:
        for n in t.get("nodes") or []:
            if not n.get("parent"):
                c = (n.get("q") or n.get("raw") or "").strip().replace("\n", " ")
                if c:
                    covers.append(c)
                break
    try:
        mtime = os.path.getmtime(st.file)
    except OSError:
        mtime = 0.0
    return {
        "path": path,
        "short": short_path(path),
        "name": os.path.basename(path) or path,
        "trees": len(trees),
        "nodes": sum(len(t.get("nodes") or []) for t in trees),
        "notes": len(data.get("notes") or []),
        "pre": " · ".join(covers)[:140],
        "mtime": mtime,
    }


def scan_projects(roots, max_depth=4, budget=9000, seconds=3.0):
    """在几个根目录下浅扫一遍，挑出所有带 .qp 的项目。"""
    t0 = time.time()
    projects, seen = [], 0
    for root in roots:
        root = os.path.abspath(os.path.expanduser(root))
        if not os.path.isdir(root):
            continue
        stack = [(root, 0)]
        while stack:
            d, depth = stack.pop()
            seen += 1
            if seen > budget or time.time() - t0 > seconds:
                stack = []
                break
            if os.path.isfile(os.path.join(d, DIRNAME, STORE)):
                p = read_project(d)
                if p:
                    projects.append(p)
                continue  # 有 qp 就不再往里钻
            if depth >= max_depth:
                continue
            try:
                entries = list(os.scandir(d))
            except OSError:
                continue
            for e in entries:
                try:
                    if not e.is_dir(follow_symlinks=False):
                        continue
                except OSError:
                    continue
                if e.name.startswith(".") or e.name in SKIP_NAMES:
                    continue
                stack.append((e.path, depth + 1))
    projects.sort(key=lambda x: -x["mtime"])
    return {"projects": projects, "scanned": seen, "roots": roots}


def cached_projects(roots, force=False):
    with _SCAN_LOCK:
        fresh = _SCAN["data"] is not None and (time.time() - _SCAN["t"] < 5.0)
        if fresh and not force and _SCAN["data"]["roots"] == roots:
            return _SCAN["data"]
    data = scan_projects(roots)
    with _SCAN_LOCK:
        _SCAN["t"] = time.time()
        _SCAN["data"] = data
    return data


def forget_scan():
    with _SCAN_LOCK:
        _SCAN["data"] = None


_PICK_LOCK = threading.Lock()
_PICKING = [False]


def pick_folder(prompt="选择项目文件夹"):
    """弹 macOS 原生的「选择文件夹」框，返回绝对路径；用户取消返回 None。

    原生框是模态的，一次只允许开一个 —— 连点两下按钮会叠出两个框，很讨厌。
    """
    with _PICK_LOCK:
        if _PICKING[0]:
            raise RuntimeError("已经有一个选择框开着了")
        _PICKING[0] = True
    try:
        osa = shutil.which("osascript") or "/usr/bin/osascript"
        script = 'POSIX path of (choose folder with prompt "%s")' % prompt
        try:
            out = subprocess.run([osa, "-e", script],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 text=True, timeout=600)
        except (OSError, subprocess.SubprocessError) as e:
            raise RuntimeError("打不开选择框：%s" % e)
        if out.returncode != 0:
            err = (out.stderr or "").strip().splitlines()
            msg = err[-1] if err else "已取消"
            if "cancel" in msg.lower() or "-128" in msg:
                return None
            raise RuntimeError(msg)
        return out.stdout.strip().rstrip("/") or "/"
    finally:
        with _PICK_LOCK:
            _PICKING[0] = False


class HomeHandler(BaseHTTPRequestHandler):
    roots = []
    home_url = ""
    servers = {}          # 项目路径 -> (url, thread)
    lock = threading.Lock()

    def _send(self, code, ctype, body):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _json(self, obj, code=200):
        self._send(code, "application/json; charset=utf-8",
                   json.dumps(obj, ensure_ascii=False).encode("utf-8"))

    def do_GET(self):
        p = urlparse(self.path).path
        if p in ("/", "/index.html"):
            self._send(200, "text/html; charset=utf-8", _asset(HOME_HTML).encode("utf-8"))
        elif p == "/api/ping":
            self._json({"ok": 1})
        elif p == "/api/projects":
            self._json(cached_projects(list(HomeHandler.roots),
                                       force=(parse_qs(urlparse(self.path).query).get("refresh"))))
        else:
            self._send(404, "text/plain; charset=utf-8", b"not found")

    def do_POST(self):
        p = urlparse(self.path).path
        if p == "/api/quit":
            self._json({"ok": 1})
            # os._exit 不走 atexit，所以退出前手动把还挂着的快照冲刷掉
            def bye():
                flush_all_snapshots()
                os._exit(0)
            threading.Timer(0.2, bye).start()
            return
        if p == "/api/browse":
            try:
                self._json({"path": pick_folder()})
            except Exception as e:
                self._json({"error": str(e) or "打不开选择框"}, 400)
            return
        if p not in ("/api/open", "/api/init"):
            self._json({"error": "not found"}, 404)
            return
        try:
            n = int(self.headers.get("Content-Length") or 0)
            req = json.loads(self.rfile.read(n).decode("utf-8") or "{}")
        except (ValueError, TypeError):
            self._json({"error": "请求体不是合法 JSON"}, 400)
            return
        path = os.path.abspath(os.path.expanduser(str(req.get("path") or "").strip()))
        try:
            if p == "/api/open":
                self._json({"url": self.open_project(path, bool(req.get("create")))})
            else:
                if not os.path.isdir(path):
                    die("目录不存在：%s" % path)
                os.makedirs(os.path.join(path, DIRNAME), exist_ok=True)
                Store(os.path.join(path, DIRNAME), snapshot=True).save()
                forget_scan()
                self._json({"ok": 1, "path": path})
        except Exception as e:
            self._json({"error": str(e) or "操作失败"}, 400)

    def open_project(self, path, create=False):
        """一个项目一台小服务，端口随手挑；同一项目复用已开的那台。

        create=True 时，目录里还没有 .qp 就地建一个 —— 免得「选择文件夹」先打一次 400。
        """
        if not os.path.isdir(path):
            die("目录不存在：%s" % path)
        if not os.path.isfile(os.path.join(path, DIRNAME, STORE)):
            if not create:
                die("这个目录里还没有 qp")
            os.makedirs(os.path.join(path, DIRNAME), exist_ok=True)
            Store(os.path.join(path, DIRNAME)).save()
            forget_scan()
        with HomeHandler.lock:
            hit = HomeHandler.servers.get(path)
            if hit:
                return hit[0]
            store = Store(os.path.join(path, DIRNAME))
            httpd, url = start_project_server(store, 8766, HomeHandler.home_url)
            t = threading.Thread(target=httpd.serve_forever, daemon=True)
            t.start()
            HomeHandler.servers[path] = (url, t)
            return url

    def log_message(self, *a):
        pass


def home_roots(args):
    return [os.path.abspath(os.path.expanduser(r))
            for r in (args.root or [os.path.expanduser("~")])]


def start_home_server(port, roots):
    """在本进程里起一台 home 服务（后台线程），返回 (url, httpd)。

    这条给 `qp app` 和 `qp home --app` 用：它们要在主线程跑原生窗口的事件循环。
    """
    HomeHandler.roots = roots
    forget_scan()
    httpd, actual = bind_server(port, HomeHandler)
    url = "http://127.0.0.1:%d/" % actual
    HomeHandler.home_url = url
    threading.Thread(target=httpd.serve_forever, daemon=True).start()
    return url, httpd


def print_home_banner(url, roots):
    print("qp home  ->  " + url)
    for r in roots:
        print("扫描     ->  " + r)
    print("")


def cmd_home(args):
    roots = home_roots(args)
    if args.app:
        url, _ = start_home_server(args.port, roots)
        print_home_banner(url, roots)
        print("窗口     ->  " + open_window(url) + "（关掉窗口就退出）")
        return
    HomeHandler.roots = roots
    forget_scan()
    httpd, port = bind_server(args.port, HomeHandler)
    url = "http://127.0.0.1:%d/" % port
    HomeHandler.home_url = url
    print_home_banner(url, roots)
    print("提示：关掉这个终端服务就停了。  Ctrl-C 停止。")
    if not args.no_open:
        threading.Timer(0.4, lambda: webbrowser.open(url)).start()
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\n已停止。")
    finally:
        httpd.server_close()


def cmd_app(args):
    """qp app：服务在跑就复用，否则就地起一个；然后用原生窗口打开。

    窗口用什么由 open_window 决定：pywebview（系统 WKWebView）> Chrome --app > 默认浏览器。
    """
    port = args.port
    url = "http://127.0.0.1:%d/" % port
    if server_alive(url):
        print("复用在跑的服务  ->  " + url)
    else:
        roots = home_roots(args)
        url, _ = start_home_server(port, roots)
        print_home_banner(url, roots)
    print("窗口     ->  " + open_window(url) + "（关掉窗口就退出）")


APP_SH = r"""#!/bin/zsh
# qp 应用外壳：起服务和开窗口的活都交给 `qp app`（默认用系统原生 WKWebView）。
# 用 exec：让本进程直接变成那个 GUI 进程，Dock / 菜单栏才认这是 qp 本体。
QP="%s"
PY="%s"
PORT=%d
[ -x "$PY" ] || PY=/usr/bin/python3
exec "$PY" "$QP" app --port "$PORT" >>/tmp/qp-app.log 2>&1
"""

APP_PLIST = r"""<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>CFBundleName</key><string>qp</string>
  <key>CFBundleDisplayName</key><string>qp</string>
  <key>CFBundleIdentifier</key><string>local.qp.home</string>
  <key>CFBundleExecutable</key><string>qp</string>
  <key>CFBundleIconFile</key><string>qp.icns</string>
  <key>CFBundlePackageType</key><string>APPL</string>
  <key>CFBundleSignature</key><string>????</string>
  <key>CFBundleInfoDictionaryVersion</key><string>6.0</string>
  <key>CFBundleShortVersionString</key><string>1.0</string>
  <key>CFBundleVersion</key><string>1</string>
  <key>LSMinimumSystemVersion</key><string>10.13</string>
  <key>LSApplicationCategoryType</key><string>public.app-category.productivity</string>
  <key>NSHighResolutionCapable</key><true/>
</dict>
</plist>
"""

ICON_NAME = "qp.icns"
LSREGISTER = ("/System/Library/Frameworks/CoreServices.framework/"
              "Frameworks/LaunchServices.framework/Support/lsregister")


def register_app(app):
    """把 app 交给 LaunchServices 和 Spotlight。

    直接往磁盘写出来的 bundle 不会自动进这两套数据库，注册一下 Finder /
    聚焦搜索（Spotlight）才认得它。
    """
    ls = shutil.which("lsregister")
    if not ls and os.path.exists(LSREGISTER):
        ls = LSREGISTER
    if ls:
        subprocess.call([ls, "-f", app],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    md = shutil.which("mdimport")
    if md:
        subprocess.call([md, app],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def cmd_install_app(args):
    dest = os.path.abspath(os.path.expanduser(args.dest or os.path.join("~", "Applications")))
    app = os.path.join(dest, "qp.app")
    contents = os.path.join(app, "Contents")
    macos = os.path.join(contents, "MacOS")
    res = os.path.join(contents, "Resources")
    os.makedirs(macos, exist_ok=True)
    os.makedirs(res, exist_ok=True)
    py = sys.executable or "/usr/bin/python3"
    me = os.path.abspath(__file__)
    exe = os.path.join(macos, "qp")
    with open(exe, "w", encoding="utf-8") as f:
        f.write(APP_SH % (me, py, args.port))
    os.chmod(exe, 0o755)
    icon = asset_path(ICON_NAME)
    if os.path.isfile(icon):
        with open(icon, "rb") as src, open(os.path.join(res, ICON_NAME), "wb") as dst:
            dst.write(src.read())
    else:
        print("提示：没找到 %s，这次生成的 app 没有图标。" % icon)
    # PkgInfo 是老式 bundle 的标记文件，有些系统组件靠它认这是正经 app
    with open(os.path.join(contents, "PkgInfo"), "w", encoding="utf-8") as f:
        f.write("APPL????")
    with open(os.path.join(contents, "Info.plist"), "w", encoding="utf-8") as f:
        f.write(APP_PLIST)
    # 本机用脚本捏出来的 app 没有签名，spctl 会报 "no usable signature"，
    # Finder / 聚焦搜索点开时可能被拦。临时签一下（ad-hoc），不行就算了。
    if shutil.which("codesign"):
        subprocess.call(["codesign", "--force", "--sign", "-", app],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    # 文件都写完了再注册，否则系统看到的是半成品
    register_app(app)
    print("已生成 " + app)
    print("双击即可用；也可以拖到程序坞。")


def cmd_img(args):
    store = cwd_store()
    nid = resolve_id(store.data, args.node)
    names = []
    for p in args.files:
        if p == "-":
            blob = sys.stdin.buffer.read()
        else:
            if not os.path.isfile(p):
                die("找不到文件 " + p)
            with open(p, "rb") as f:
                blob = f.read()
        if not blob:
            die("空文件 " + p)
        names.append(save_image(store, blob))
    for nm in names:
        op_add_img(store, nid, nm)
    print("已加入 %d 张图到 %s" % (len(names), nid))


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def cmd_init(args):
    store = cwd_store(create=True)
    if not os.path.exists(store.file):
        store.save()
    print("已初始化 " + store.root)
    print("存储   " + store.file)
    print("说明： .qp 以点开头，Finder / 普通 ls 默认不显示（Finder 按 ⌘⇧. 可切换）")
    print("下一步 qp new \"你最初想问什么\"")


def cmd_new(args):
    store = cwd_store(create=True)
    nid = op_new_tree(store, args.raw, args.source or "")
    print("新建树，根节点 " + nid)


def _read_md(src):
    if src == "-":
        return sys.stdin.read()
    if not os.path.isfile(src):
        die("找不到文件 " + src)
    with open(src, "r", encoding="utf-8") as f:
        return f.read()


def cmd_note(args):
    """新建一篇笔记；--export 导出、--set 换正文。"""
    store = cwd_store(create=True)
    if args.export:
        p = find_note(store.data, args.export)
        if p is None:
            die("找不到笔记 %r" % args.export)
        text = note_markdown(p)
        if args.out:
            with open(args.out, "w", encoding="utf-8") as f:
                f.write(text)
            print("已写出 " + args.out)
        else:
            print(text, end="")
        return
    if args.set_id:
        op_set_note(store, args.set_id,
                    " ".join(args.title) if args.title else None,
                    _read_md(args.md) if args.md else None)
        print("已更新笔记 " + args.set_id)
        return
    nid = op_new_note(store, " ".join(args.title or []), _read_md(args.md) if args.md else "")
    print("新建笔记 " + nid)
    print("写正文：在 qp app 里点开它")


def cmd_notes(args):
    store = cwd_store()
    notes = store.data.get("notes") or []
    if not notes:
        print("（还没有笔记）")
        return
    for p in notes:
        body = [ln for ln in (p.get("md") or "").splitlines() if ln.strip()]
        pre = body[0].strip().lstrip("# ").strip()[:52] if body else ""
        print("%-6s %-26s %s" % (p["id"], (p.get("title") or "")[:26], pre))


def cmd_add(args):
    store = cwd_store()
    pid = resolve_id(store.data, args.node) if args.node else store.data.get("focus")
    if not pid:
        die("没有焦点节点，指定一个父节点：qp add <id> \"...\"")
    nid = op_add(store, pid, args.raw)
    print("已挂到 " + pid + " 下，新节点 " + nid)


def cmd_edit(args):
    store = cwd_store()
    nid = resolve_id(store.data, args.node)
    op_edit(store, nid, args.raw)
    print("已更新 " + nid)


def cmd_close(args):
    store = cwd_store()
    nid = resolve_id(store.data, args.node)
    blocker, resolution = args.blocker or "", args.resolution or ""
    if args.llm:
        cfg = load_cfg(store.root)
        tree, node = find_node(store.data, nid)
        parent = None
        if node.get("parent"):
            parent = [x for x in tree["nodes"] if x["id"] == node["parent"]]
            parent = parent[0] if parent else None
        chain = path_to(store.data, nid)
        lines = ["  " * i + "- " + (x.get("q") or x.get("raw", "")) for i, x in enumerate(chain)]
        out = llm_chat(cfg, PROMPT_CLOSE % (
            (parent.get("q") or parent.get("raw")) if parent else "（这是根节点）",
            "\n".join(lines)))
        for ln in out.splitlines():
            ln = ln.strip()
            if ln.startswith("卡点"):
                blocker = ln.split("：", 1)[-1].split(":", 1)[-1].strip()
            elif ln.startswith("已明白"):
                resolution = ln.split("：", 1)[-1].split(":", 1)[-1].strip()
        print(out)
    if not blocker and not resolution:
        print("（未给 --blocker / --resolution，仅标记为已收口）")
    op_close(store, nid, blocker, resolution)
    print("已收口 " + nid)


def cmd_reopen(args):
    store = cwd_store()
    nid = resolve_id(store.data, args.node)
    op_reopen(store, nid)
    print("已重新打开 " + nid)


def cmd_rm(args):
    store = cwd_store()
    nid = resolve_id(store.data, args.node)
    gone = op_delete(store, nid)
    print("已删除 %d 个节点：%s" % (len(gone), " ".join(gone)))


def cmd_focus(args):
    store = cwd_store()
    nid = resolve_id(store.data, args.node) if args.node else None
    op_focus(store, nid)
    if nid:
        _, node = find_node(store.data, nid)
        print("焦点 -> " + label(node))
    else:
        print("焦点已清空")


def cmd_reset(args):
    store = cwd_store()
    nid = resolve_id(store.data, args.node) if args.node else None
    n = op_reset_pos(store, nid)
    print("已复位 %d 个节点，回到自动布局" % n)


def cmd_tree(args):
    store = cwd_store()
    data = store.data
    if not data["trees"]:
        print("（还没有树）")
        return
    ids = getattr(args, "ids", False)
    if args.tree:
        print(ascii_tree(tree_by_token(data, args.tree), ids))
        return
    for t in data["trees"]:
        print(ascii_tree(t, ids))
        print()


def tree_by_token(data, token):
    for t in data["trees"]:
        if t["id"] == token:
            return t
    for t in data["trees"]:
        if t["id"].startswith(token):
            return t
    die("找不到树 %r" % token)


def cmd_path(args):
    store = cwd_store()
    nid = resolve_id(store.data, args.node)
    chain = path_to(store.data, nid)
    if not chain:
        die("找不到节点")
    for i, n in enumerate(chain):
        print("%s%s%s" % ("  " * i, label(n),
                          "  ✓" if n.get("status") == "closed" else ""))


def cmd_render(args):
    store = cwd_store()
    p = write_snapshot(store)
    print("已写出静态快照 " + p)
    print("可直接双击打开（只读）。")


def cmd_md(args):
    store = cwd_store()
    text = doc_markdown(store.data, args.tree)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(text)
        print("已写出 " + os.path.abspath(args.out))
    else:
        sys.stdout.write(text)


def cmd_llm(args):
    """配置 / 查看 / 试跑模型。不给参数就报状态 —— 省得还要去翻文档。"""
    store = cwd_store(create=True)
    root = store.root

    if args.list:
        print("可选预设（用法：qp llm --preset <名字> --key sk-xxx [--global]）\n")
        for name in PRESETS:
            p = PRESETS[name]
            print("  " + name)
            print("    地址  " + p["endpoint"])
            print("    模型  " + p["model"])
            if p.get("params"):
                print("    附加  " + json.dumps(p["params"], ensure_ascii=False))
            print("    备注  " + p["note"] + "\n")
        print("免费额度和模型名时常会变；配完跑 `qp llm --test` 验一下。")
        print("加 --global 写到 " + GLOBAL_CFG + "，所有项目共用一份。")
        return

    dest = GLOBAL_CFG if args.globally else cfg_path(root)
    changed = {}
    if args.preset:
        if args.preset not in PRESETS:
            die("没有这个预设：%s（跑 `qp llm --list` 看有哪些）" % args.preset)
        changed["preset"] = args.preset
    for k, v in (("endpoint", args.endpoint), ("api_key", args.key), ("model", args.model)):
        if v:
            changed[k] = v
    if changed:
        cur = read_cfg_file(dest)
        cur.update(changed)
        print("已写入 " + save_cfg_file(dest, cur))
        if not args.globally and os.path.realpath(dest) != os.path.realpath(GLOBAL_CFG) \
                and os.path.exists(GLOBAL_CFG):
            print("（全局那份 " + GLOBAL_CFG + " 也在，本项目这份优先）")

    cfg = load_cfg(root)
    print("地址  " + (cfg.get("endpoint") or "(未设置)"))
    print("模型  " + (cfg.get("model") or "(未设置)"))
    print("密钥  " + (("已设置（%d 字符）" % len(cfg["api_key"])) if cfg.get("api_key") else "(未设置)"))
    if cfg.get("params"):
        print("附加  " + json.dumps(cfg["params"], ensure_ascii=False))
    files = cfg_sources(root)
    print("来源  " + (" + ".join(files) if files else "（还没写过任何配置文件）"))
    if not (cfg.get("endpoint") and cfg.get("api_key")):
        print("")
        print(LLM_HELP)
        return
    if not args.test:
        print("\n加 --test 可以真发一句，顺便看延迟。")
        return
    print("\n试一句…")
    t0 = time.time()
    try:
        out = llm_chat(cfg, "只回四个字：连接正常", timeout=args.timeout)
    except RuntimeError as e:
        die(str(e))
    print("回话  " + out.replace("\n", " "))
    print("延迟  %.2fs" % (time.time() - t0))


def cmd_ui(args):
    store = cwd_store(create=True)
    if not os.path.exists(store.file):
        store.save()
    serve(store, args.port, not args.no_open)


def cmd_where(args):
    root = os.path.join(os.getcwd(), DIRNAME)
    print(root)
    print("存在" if os.path.isdir(root) else "不存在（先跑 qp init）")
    store = Store(root) if os.path.isdir(root) else None
    if store:
        print(store.file)
        print("树数量 %d" % len(store.data["trees"]))


def build_parser():
    p = argparse.ArgumentParser(
        prog="qp",
        description="qp - 追问树：记录你为什么会问这个问题，随时回到主线。",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""示例
  qp init
  qp new "saliency 加权到底怎么做的" --source "arXiv:2410.10877 p.5"
  qp add @ "SAM 不是要 prompt 吗，这里凭什么直接用"
  qp tree
  qp close @ --blocker "父节点默认 SAM 能零样本" --resolution "它用的是自动 mask 生成"
  qp md -o notes.md      导出 markdown
  qp img @ figure.png    给节点贴图（也可以直接在界面里 ⌘V 粘贴）
  qp note "读这篇的笔记"   新建一篇 markdown 笔记（和树并列）
  qp notes               列出所有笔记
  qp llm --preset zhipu --key sk-xxx --global   配上模型，全局共用（AI 梳理 / 界面里的对话用它）
  qp llm --test          试一句，顺便看延迟
  qp ui           打开带气泡树的图形界面
  qp home         打开项目管理器
  qp app          用原生窗口打开（pywebview，不依赖 Chrome）
  qp install-app  生成可双击的 qp.app
""")
    p.add_argument("-v", "--version", action="version", version="qp " + str(VERSION))
    sub = p.add_subparsers(dest="cmd")

    s = sub.add_parser("init", help="在当前目录创建 .qp/")
    s.set_defaults(func=cmd_init)

    s = sub.add_parser("new", help="新建一棵树")
    s.add_argument("raw", help="根节点：你最初想问什么")
    s.add_argument("--source", help="来源：论文 / 页码 / 链接")
    s.set_defaults(func=cmd_new)

    s = sub.add_parser("note", help="新建一篇 markdown 笔记（和树并列）")
    s.add_argument("title", nargs="*", help="新建时的标题")
    s.add_argument("-m", "--md", help="正文来源：文件路径，或 - 表示标准输入")
    s.add_argument("--export", metavar="ID", help="导出某篇笔记（默认打到标准输出）")
    s.add_argument("--set", dest="set_id", metavar="ID", help="替换某篇笔记的标题/正文")
    s.add_argument("-o", "--out", help="配合 --export：写到文件")
    s.set_defaults(func=cmd_note)

    s = sub.add_parser("notes", help="列出所有笔记")
    s.set_defaults(func=cmd_notes)

    s = sub.add_parser("add", help="给某个节点加一个子问题")
    s.add_argument("node", nargs="?", help="父节点 id，省略则挂到当前焦点")
    s.add_argument("raw", help="这个子问题是什么")
    s.set_defaults(func=cmd_add)

    s = sub.add_parser("edit", help="改某个节点的原话")
    s.add_argument("node")
    s.add_argument("raw")
    s.set_defaults(func=cmd_edit)

    s = sub.add_parser("close", help="收口：记下卡点与已明白")
    s.add_argument("node")
    s.add_argument("--blocker", help="卡点：父节点里哪个说法没懂")
    s.add_argument("--resolution", help="已明白：一句话总结")
    s.add_argument("--llm", action="store_true", help="让模型起草，需要 config.json")
    s.set_defaults(func=cmd_close)

    s = sub.add_parser("reopen", help="把已收口的节点重新打开")
    s.add_argument("node")
    s.set_defaults(func=cmd_reopen)

    s = sub.add_parser("rm", help="删除节点及其整棵子树")
    s.add_argument("node")
    s.set_defaults(func=cmd_rm)

    s = sub.add_parser("focus", help="设置当前焦点")
    s.add_argument("node", nargs="?")
    s.set_defaults(func=cmd_focus)

    s = sub.add_parser("ls", help="同 qp tree --ids（列出节点 id）")
    s.add_argument("tree", nargs="?")
    s.set_defaults(func=cmd_tree, ids=True)

    s = sub.add_parser("tree", help="打印成 ascii 树")
    s.add_argument("tree", nargs="?")
    s.add_argument("--ids", action="store_true", help="顺带显示节点 id")
    s.set_defaults(func=cmd_tree)

    s = sub.add_parser("reset", help="清掉手工拖动的坐标，回到自动布局")
    s.add_argument("node", nargs="?", help="只复位这个节点；省略则复位整棵树")
    s.set_defaults(func=cmd_reset)

    s = sub.add_parser("path", help="打印某个节点从根到它的路径")
    s.add_argument("node")
    s.set_defaults(func=cmd_path)

    s = sub.add_parser("render", help="写出静态 HTML 快照到 .qp/index.html")
    s.set_defaults(func=cmd_render)

    s = sub.add_parser("md", help="导出 markdown")
    s.add_argument("tree", nargs="?", help="只导这一棵；省略则全部")
    s.add_argument("-o", "--out", help="写到文件；不给就打到标准输出")
    s.set_defaults(func=cmd_md)

    s = sub.add_parser("img", help="给节点贴图片")
    s.add_argument("node", help="节点 id；@ 表示当前焦点")
    s.add_argument("files", nargs="+", help="图片路径； - 表示从标准输入读")
    s.set_defaults(func=cmd_img)

    s = sub.add_parser("llm", help="配置 / 查看 / 试跑对话用的模型")
    s.add_argument("--list", action="store_true", help="列出内置的几个免费预设")
    s.add_argument("--preset", help="用哪个预设（siliconflow / zhipu / dashscope / modelscope / groq）")
    s.add_argument("--key", help="API Key（会写进 .qp/config.json）")
    s.add_argument("--endpoint", help="自定义接口地址，填到 /v1 就行")
    s.add_argument("--model", help="模型名")
    s.add_argument("--global", dest="globally", action="store_true",
                   help="写到 ~/.qp/config.json，所有项目共用（项目里那份仍然优先）")
    s.add_argument("--test", action="store_true", help="真发一句，验证配置顺便看延迟")
    s.add_argument("--timeout", type=float, default=60)
    s.set_defaults(func=cmd_llm)

    s = sub.add_parser("ui", help="启动本地图形界面")
    s.add_argument("--port", type=int, default=8765)
    s.add_argument("--no-open", action="store_true")
    s.set_defaults(func=cmd_ui)

    s = sub.add_parser("home", help="项目管理器：看哪些项目有 qp，点开就进")
    s.add_argument("--port", type=int, default=8790)
    s.add_argument("--root", action="append", help="要扫描的目录，可重复；默认整个用户目录")
    s.add_argument("--app", action="store_true",
                   help="用独立窗口打开（优先系统原生窗口，退回 Chrome）")
    s.add_argument("--no-open", action="store_true")
    s.set_defaults(func=cmd_home)

    s = sub.add_parser("app", help="以原生窗口打开 qp（pywebview，不依赖 Chrome）")
    s.add_argument("--port", type=int, default=8790)
    s.add_argument("--root", action="append", help="要扫描的目录，可重复；默认整个用户目录")
    s.set_defaults(func=cmd_app)

    s = sub.add_parser("install-app", help="生成可双击的 qp.app")
    s.add_argument("--dest", help="安装到哪，默认 ~/Applications")
    s.add_argument("--port", type=int, default=8790)
    s.set_defaults(func=cmd_install_app)

    s = sub.add_parser("where", help="打印当前目录的 .qp 路径")
    s.set_defaults(func=cmd_where)

    s = sub.add_parser("help", help="打印这份帮助")
    s.set_defaults(func=lambda a: p.print_help())

    return p


def main(argv=None):
    parser = build_parser()
    args = parser.parse_args(argv)
    if not getattr(args, "cmd", None):
        parser.print_help()
        return 0
    try:
        require_assets()
        args.func(args)
    except KeyboardInterrupt:
        return 130
    except (QPError, RuntimeError) as e:
        sys.stderr.write("qp: " + str(e) + "\n")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
