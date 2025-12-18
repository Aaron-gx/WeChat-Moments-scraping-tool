# -*- coding: utf-8 -*-
import os, sys, json, time, math, threading, tempfile, datetime, queue, shutil
from collections import defaultdict
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinter import font as tkfont
import psutil
from pywinauto.application import Application
import pandas as pd
import networkx as nx
import matplotlib.pyplot as plt
import matplotlib

matplotlib.rcParams['font.sans-serif'] = ['SimHei', 'Microsoft YaHei']
matplotlib.rcParams['axes.unicode_minus'] = False

try:
    import community as community_louvain
except Exception:
    community_louvain = None

try:
    from rapidfuzz import fuzz, process as rf_process

    HAVE_RAPIDFUZZ = True
except Exception:
    HAVE_RAPIDFUZZ = False

# -------------------------
# 全局配置
# -------------------------
APP_TITLE = "微信朋友圈关系分析 专业版"
TEMP_DIR = os.path.join(tempfile.gettempdir(), "wmnt_pro_tmp")
if not os.path.exists(TEMP_DIR):
    os.makedirs(TEMP_DIR, exist_ok=True)

LIKE_WEIGHT = 1
COMMENT_WEIGHT = 2
BG_COLOR = "#f5f5f5"
FG_COLOR = "#333333"
ACCENT_COLOR = "#0066cc"
BUTTON_COLOR = "#0066cc"
FONT_NAME = "Microsoft YaHei"
FONT_SIZE_LOG = 12
FONT_SIZE_LABEL = 11


# -------------------------
# UILogHandler
# -------------------------
class UILogHandler:
    def __init__(self, data_text_widget, sys_text_widget):
        self.data_widget = data_text_widget
        self.sys_widget = sys_text_widget
        self.queue = queue.Queue()

    def log_data(self, msg):
        self.queue.put(("data", str(msg)))

    def log_sys(self, msg):
        self.queue.put(("sys", str(msg)))

    def flush_to_widgets(self):
        processed = 0
        while True:
            try:
                typ, msg = self.queue.get_nowait()
            except queue.Empty:
                break
            ts = datetime.datetime.now().strftime("%H:%M:%S")
            if typ == "data":
                try:
                    self.data_widget.configure(state='normal')
                    self.data_widget.insert('end', f"[{ts}] {msg}\n")
                    self.data_widget.see('end')
                    self.data_widget.configure(state='disabled')
                except Exception:
                    pass
            else:
                try:
                    self.sys_widget.configure(state='normal')
                    self.sys_widget.insert('end', f"[{ts}] {msg}\n")
                    self.sys_widget.see('end')
                    self.sys_widget.configure(state='disabled')
                except Exception:
                    pass
            processed += 1
        return processed


# -------------------------
# 微信采集相关
# -------------------------
def get_wechat_pid():
    for proc in psutil.process_iter(['pid', 'name']):
        try:
            name = proc.info.get('name') or ''
            if name.lower() == 'wechat.exe':
                return proc.info['pid']
        except Exception:
            continue
    return None


def extract_likes_from_element(post_element):
    candidates = []

    def search(el, depth=0):
        if depth > 15:
            return
        try:
            for c in el.children():
                try:
                    ctrl_type = c.element_info.control_type
                    name = c.element_info.name or c.window_text()
                except Exception:
                    continue
                if (ctrl_type in ("Static", "Text")
                        and name and '，' in name
                        and ':' not in name and '：' not in name
                        and 4 < len(name) < 300
                        and not any(x in name for x in ['包含', '张图片', '个视频', '回复'])):
                    candidates.append((depth, name))
                search(c, depth + 1)
        except Exception:
            pass

    try:
        search(post_element)
        if not candidates:
            return ""
        candidates.sort(key=lambda x: x[0], reverse=True)
        return candidates[0][1]
    except Exception:
        return ""


def extract_comments_from_element(post_element):
    def search(el, depth=0):
        if depth > 12:
            return []
        try:
            for c in el.children():
                try:
                    ctrl_type = c.element_info.control_type
                    name = c.element_info.name
                except Exception:
                    continue
                if ctrl_type == "List" and (name == "评论" or name == "评论列表"):
                    items = c.children(control_type="ListItem")
                    return [i.window_text() for i in items if i.window_text()]
                res = search(c, depth + 1)
                if res:
                    return res
        except Exception:
            pass
        return []

    try:
        return search(post_element) or []
    except Exception:
        return []


def parse_moments_collect(target_count=100, timeout=5, progress_callback=None, log_sys=None, log_data=None):
    if log_sys: log_sys(f"开始采集（目标 {target_count} 条，超时 {timeout}s）")
    pid = get_wechat_pid()
    if not pid:
        raise RuntimeError("未检测到 WeChat.exe 进程，请启动微信桌面客户端。")
    app = Application(backend='uia').connect(process=pid)
    moments_window = None
    try:
        moments_window = app['朋友圈']
    except Exception:
        for w in app.windows():
            try:
                if '朋友圈' in (w.window_text() or ''):
                    moments_window = w
                    break
            except Exception:
                continue
    if not moments_window:
        raise RuntimeError("无法定位朋友圈窗口，请打开微信并进入朋友圈页面。")
    moments_list = None
    try:
        moments_list = moments_window.child_window(title="朋友圈", control_type="List")
    except Exception:
        try:
            lists = [c for c in moments_window.children() if c.element_info.control_type == 'List']
            moments_list = lists[0] if lists else None
        except Exception:
            moments_list = None
    if not moments_list:
        raise RuntimeError("朋友圈列表控件未找到，请确保页面处于朋友圈界面（中文）。")
    all_posts = []
    seen = set()
    scroll_delay = 0.45
    last_new = time.time()
    while len(all_posts) < target_count:
        try:
            posts = moments_list.children(control_type="ListItem")
        except Exception:
            posts = []
        new_found = False
        for p in posts:
            try:
                text = p.window_text()
            except Exception:
                continue
            if not text or text in seen:
                continue
            seen.add(text)
            new_found = True
            last_new = time.time()
            lines = [l.strip() for l in text.split('\n') if l.strip()]
            if len(lines) < 2:
                continue
            publisher = lines[0].rstrip(':').strip()
            content = lines[1]
            time_str = lines[-1]
            if len(lines) >= 3 and "包含" in lines[-2] and "图片" in lines[-2]:
                content += " (" + lines[-2] + ")"
            likes = extract_likes_from_element(p) or ""
            comments = extract_comments_from_element(p) or []
            item = {"编号": len(all_posts) + 1, "发布者": publisher, "内容": content, "时间": time_str, "点赞": likes,
                    "评论": comments}
            all_posts.append(item)
            if progress_callback:
                try:
                    progress_callback(len(all_posts), target_count)
                except Exception:
                    pass
            if log_data: log_data(f"采集到第 {len(all_posts)} 条：{publisher}")
            if len(all_posts) >= target_count:
                break
        try:
            moments_list.type_keys("{DOWN}")
        except Exception:
            pass
        time.sleep(scroll_delay)
        if time.time() - last_new > timeout:
            if log_sys: log_sys(f"超时 {timeout}s 未发现新动态，停止采集。")
            break
    if log_sys: log_sys(f"采集结束，共 {len(all_posts)} 条。")
    return all_posts


# -------------------------
# 网络构建与分析
# -------------------------
def build_interaction_graph(publishers, all_posts=None, like_weight=LIKE_WEIGHT, comment_weight=COMMENT_WEIGHT,
                            alias_map=None, log_sys=None):
    """从所有数据列构建互动网络（发布者、点赞者、评论者）"""
    if log_sys: log_sys("构建互动网络（基于所有互动数据）...")
    G = nx.Graph()

    def norm(name):
        if not name: return ""
        name = str(name).strip()
        if alias_map and name in alias_map:
            return alias_map[name]
        return name

    # 添加发布者作为节点
    for pub in publishers:
        pub = norm(pub)
        # 过滤掉包含'回复'的名称
        if pub and '回复' not in pub:
            G.add_node(pub)

    # 如果提供了完整的posts数据，构建完整互动网络
    if all_posts:
        for post in all_posts:
            pub = norm(post.get('发布者', ''))
            if not pub:
                continue
            if pub not in G:
                G.add_node(pub)

            # 点赞关系
            likes_raw = post.get('点赞', '')
            if isinstance(likes_raw, str) and likes_raw.strip():
                likers = [x.strip() for x in likes_raw.replace('、', '，').split('，') if x.strip()]
                for liker in likers:
                    liker = norm(liker)
                    # 过滤掉包含'回复'的名称
                    if not liker or liker == pub or '回复' in liker:
                        continue
                    if liker not in G:
                        G.add_node(liker)
                    if G.has_edge(liker, pub):
                        G[liker][pub]['weight'] += like_weight
                        G[liker][pub]['likes'] = G[liker][pub].get('likes', 0) + 1
                    else:
                        G.add_edge(liker, pub, weight=like_weight, likes=1, comments=0)

            # 评论关系
            comments = post.get('评论', []) or []
            for comment in comments:
                if not comment:
                    continue
                commenter = None
                if ':' in comment:
                    commenter = comment.split(':', 1)[0].strip()
                elif '：' in comment:
                    commenter = comment.split('：', 1)[0].strip()
                else:
                    parts = comment.split(None, 1)
                    commenter = parts[0].strip() if parts else comment.strip()

                commenter = norm(commenter)
                # 过滤掉包含'回复'的名称
                if not commenter or commenter == pub or '回复' in commenter:
                    continue
                if commenter not in G:
                    G.add_node(commenter)
                if G.has_edge(commenter, pub):
                    G[commenter][pub]['weight'] += comment_weight
                    G[commenter][pub]['comments'] = G[commenter][pub].get('comments', 0) + 1
                else:
                    G.add_edge(commenter, pub, weight=comment_weight, likes=0, comments=1)

    # 收集所有参与者用于计数
    all_participants = set(publishers)
    if all_posts:
        for post in all_posts:
            likes_raw = post.get('点赞', '')
            if isinstance(likes_raw, str) and likes_raw.strip():
                likers = [x.strip() for x in likes_raw.replace('、', '，').split('，') if x.strip()]
                all_participants.update(likers)

            comments = post.get('评论', []) or []
            for comment in comments:
                if ':' in comment:
                    commenter = comment.split(':', 1)[0].strip()
                elif '：' in comment:
                    commenter = comment.split('：', 1)[0].strip()
                else:
                    parts = comment.split(None, 1)
                    commenter = parts[0].strip() if parts else comment.strip()
                if commenter:
                    all_participants.add(commenter)

    pub_counts = defaultdict(int)
    for pub in publishers:
        pub = norm(pub)
        if pub:
            pub_counts[pub] += 1

    if log_sys: log_sys(f"网络构建完成：节点 {G.number_of_nodes()}，边 {G.number_of_edges()}")
    return G, pub_counts


def analyze_graph(G, pub_counts, all_posts, use_louvain=True, log_sys=None):
    """分析网络图"""
    if log_sys: log_sys("开始网络分析...")
    res = {}
    res['num_nodes'] = G.number_of_nodes()
    res['num_edges'] = G.number_of_edges()

    # 基于图的度计算活跃度
    degree_dict = dict(G.degree())
    res['degree'] = degree_dict

    # 度中心性（活跃度排序）
    try:
        res['degree_centrality'] = nx.degree_centrality(G)
    except Exception as e:
        res['degree_centrality'] = {}
        if log_sys: log_sys(f"度中心性计算失败: {e}")

    # 介数中心性
    res['betweenness'] = {}
    n = G.number_of_nodes()
    if n > 2:
        try:
            if n <= 400:
                if log_sys: log_sys("计算介数中心性（精确）...")
                res['betweenness'] = nx.betweenness_centrality(G, normalized=True)
            else:
                k = min(200, max(80, n // 10))
                if log_sys: log_sys(f"计算介数中心性（近似，采样 k={k}）...")
                res['betweenness'] = nx.betweenness_centrality(G, k=k, normalized=True, seed=42)
        except Exception as e:
            res['betweenness'] = {}
            if log_sys: log_sys(f"介数计算失败: {e}")

    # 社区检测：基于完整互动网络
    res['communities'] = {}
    res['community_groups'] = {}

    if use_louvain and community_louvain:
        try:
            if log_sys: log_sys("开始社区检测（基于完整互动网络）...")
            if G.number_of_nodes() > 0:
                partition = community_louvain.best_partition(G)
                res['communities'] = partition
                cg = {}
                for node, cid in partition.items():
                    cg.setdefault(cid, []).append(node)
                res['community_groups'] = cg
                if log_sys: log_sys(f"社区检测完成：{len(cg)} 个社区")
        except Exception as e:
            if log_sys: log_sys(f"社区检测失败: {e}")
    else:
        if use_louvain:
            if log_sys: log_sys("未安装 python-louvain，跳过社区检测。")

    def topk(dct, k=10):
        if not dct:
            return []
        try:
            k = int(k)
        except:
            k = 10
        if k <= 0:
            k = 10
        items = sorted(dct.items(), key=lambda x: x[1], reverse=True)
        return items[:k]

    res['top_degree'] = topk(res.get('degree_centrality', {}), k=10)
    res['top_betweenness'] = topk(res.get('betweenness', {}), k=10)

    res['network_density'] = nx.density(G) if G.number_of_nodes() > 0 else 0

    # 计算网络统计
    weights = [G[u][v].get('weight', 1) for u, v in G.edges()]
    res['avg_weight'] = sum(weights) / len(weights) if weights else 0
    res['max_weight'] = max(weights) if weights else 0

    if log_sys: log_sys("网络分析完成。")
    return res


# -------------------------
# 增强分析功能
# -------------------------
def analyze_publisher_activity(all_posts):
    """分析发布者的活跃度（仅基于发布者列）"""
    activity = defaultdict(lambda: {'posts': 0, 'total_interactions': 0})

    for post in all_posts:
        publisher = post.get('发布者', '')
        if publisher:
            activity[publisher]['posts'] += 1

            # 计算该条发布获得的互动数
            likes_raw = post.get('点赞', '')
            likes_count = 0
            if isinstance(likes_raw, str) and likes_raw.strip():
                likes_count = len([x.strip() for x in likes_raw.replace('、', '，').split('，') if x.strip()])

            comments = post.get('评论', []) or []
            comments_count = len(comments) if isinstance(comments, list) else 0

            activity[publisher]['total_interactions'] += likes_count + comments_count

    return dict(activity)


# -------------------------
# 导出功能
# -------------------------
def format_time_display(time_str):
    """处理时间显示：将时间转换为相对时间显示"""
    try:
        from datetime import datetime, date, timedelta
        time_str = str(time_str).strip()
        now = datetime.now()
        today = now.date()

        if any(k in time_str for k in ['前', '昨天', '刚刚']):
            return time_str

        if ':' in time_str and '月' not in time_str and '年' not in time_str:
            try:
                return f"今天 {time_str}"
            except Exception:
                pass

        if '月' in time_str and '日' in time_str and '年' not in time_str:
            try:
                parsed_dt = datetime.strptime(f"{now.year}-{time_str}", "%Y-%m月%d日")
                if parsed_dt.date() > today:
                    parsed_dt = datetime.strptime(f"{now.year - 1}-{time_str}", "%Y-%m月%d日")

                parsed_date = parsed_dt.date()
                delta = today - parsed_date
                if delta.days == 0:
                    return "今天"
                if delta.days == 1:
                    return "昨天"
                if delta.days < 30:
                    return f"{delta.days}天前"
                else:
                    return time_str
            except Exception:
                return time_str

        if '年' in time_str and '月' in time_str and '日' in time_str:
            try:
                parsed_date = datetime.strptime(time_str, "%Y年%m月%d日").date()
                delta = today - parsed_date
                if delta.days == 0:
                    return "今天"
                if delta.days == 1:
                    return "昨天"
                return f"{delta.days}天前"
            except Exception:
                return time_str

        return time_str
    except Exception:
        return str(time_str)


# -------------------------
# 别名处理
# -------------------------
def suggest_aliases_from_publishers(all_posts, threshold=0.86, max_pairs=1000):
    """从所有数据列进行别名建议（发布者、点赞者、评论者）"""
    names = set()

    # 收集发布者
    for post in all_posts:
        pub = post.get('发布者', '')
        if pub and pub.strip():
            names.add(pub.strip())

    # 收集点赞者
    for post in all_posts:
        likes_raw = post.get('点赞', '')
        if isinstance(likes_raw, str) and likes_raw.strip():
            likers = [x.strip() for x in likes_raw.replace('、', '，').split('，') if x.strip()]
            for liker in likers:
                names.add(liker)

    # 收集评论者
    for post in all_posts:
        comments = post.get('评论', []) or []
        for comment in comments:
            if ':' in comment:
                commenter = comment.split(':', 1)[0].strip()
            elif '：' in comment:
                commenter = comment.split('：', 1)[0].strip()
            else:
                parts = comment.split(None, 1)
                commenter = parts[0].strip() if parts else comment.strip()
            if commenter:
                names.add(commenter)

    names = list(names)
    suggestions = []

    if HAVE_RAPIDFUZZ:
        for i, name in enumerate(names):
            matches = rf_process.extract(name, names, scorer=fuzz.ratio, limit=10)
            for m_name, score, _ in matches:
                if m_name == name: continue
                ratio = score / 100.0
                if ratio >= threshold:
                    suggestions.append((name, m_name, ratio))
            if len(suggestions) > max_pairs:
                break
    else:
        import difflib
        n = len(names)
        for i in range(n):
            for j in range(i + 1, n):
                a = names[i];
                b = names[j]
                ratio = difflib.SequenceMatcher(None, a, b).ratio()
                if ratio >= threshold:
                    suggestions.append((a, b, ratio))
                if len(suggestions) > max_pairs:
                    break
            if len(suggestions) > max_pairs:
                break
    suggestions.sort(key=lambda x: x[2], reverse=True)
    return suggestions


def build_alias_map_from_suggestions(suggestions, prefer_shorter=True):
    amap = {}
    for a, b, score in suggestions:
        if prefer_shorter:
            can = a if len(a) <= len(b) else b
            alt = b if can == a else a
        else:
            can, alt = a, b
        if alt in amap:
            continue
        if alt == can:
            continue
        amap[alt] = can
    return amap


# -------------------------
# GUI 主体
# -------------------------
class MomentsApp:
    def __init__(self, master):
        self.master = master
        master.title(APP_TITLE)
        master.geometry("1400x900")
        master.configure(bg=BG_COLOR)

        self.all_posts = []
        self.graph = None
        self.analysis = None
        self.alias_map = {}
        self.last_suggestions = []
        self.temp_dir = TEMP_DIR

        self._build_ui()
        self.ui_logger = UILogHandler(self.data_text, self.sys_text)
        self._schedule_ui_log_flush()

    def _build_ui(self):
        # 顶部工具栏
        top_frame = ttk.Frame(self.master)
        top_frame.pack(fill='x', padx=10, pady=10)

        # 第一行：采集参数
        row1 = ttk.Frame(top_frame)
        row1.pack(fill='x', pady=5)
        ttk.Label(row1, text="采集数量", font=(FONT_NAME, FONT_SIZE_LABEL)).pack(side='left', padx=5)
        self.entry_count = ttk.Entry(row1, width=8)
        self.entry_count.insert(0, "200")
        self.entry_count.pack(side='left', padx=2)

        ttk.Label(row1, text="超时(s)", font=(FONT_NAME, FONT_SIZE_LABEL)).pack(side='left', padx=5)
        self.entry_timeout = ttk.Entry(row1, width=6)
        self.entry_timeout.insert(0, "6")
        self.entry_timeout.pack(side='left', padx=2)

        ttk.Label(row1, text="导出格式", font=(FONT_NAME, FONT_SIZE_LABEL)).pack(side='left', padx=5)
        self.combo_format = ttk.Combobox(row1, values=["json", "xlsx"], width=8, state="readonly")
        self.combo_format.set("json")
        self.combo_format.pack(side='left', padx=2)

        ttk.Label(row1, text="保存路径", font=(FONT_NAME, FONT_SIZE_LABEL)).pack(side='left', padx=5)
        self.entry_path = ttk.Entry(row1, width=50)
        self.entry_path.insert(0, f"moments_{datetime.date.today()}.json")
        self.entry_path.pack(side='left', padx=2)
        ttk.Button(row1, text="浏览...", command=self.choose_save_path).pack(side='left', padx=2)

        # 第二行：主要按钮
        btn_frame = ttk.Frame(top_frame)
        btn_frame.pack(fill='x', pady=8)

        button_configs = [
            ("开始采集", self.start_collect),
            ("导入数据", self.import_file),
            ("关系网分析", self.start_analyze),
            ("查看关系图", self.show_network_graph),
            ("别名建议", self.run_alias_suggestion),
            ("应用别名", self.apply_alias_map),
            ("使用手册", self.show_data_interpretation),
        ]

        for text, command in button_configs:
            ttk.Button(btn_frame, text=text, command=command, width=14).pack(side='left', padx=3)

        # 进度条
        progress_frame = ttk.Frame(self.master)
        progress_frame.pack(fill='x', padx=10, pady=5)
        ttk.Label(progress_frame, text="进度:", font=(FONT_NAME, FONT_SIZE_LABEL)).pack(side='left', padx=5)
        self.progress_var = tk.DoubleVar()
        self.progress = ttk.Progressbar(progress_frame, variable=self.progress_var, maximum=100, length=1000)
        self.progress.pack(side='left', fill='x', expand=True, padx=5)

        # 主体内容区
        main_pane = ttk.PanedWindow(self.master, orient='vertical')
        main_pane.pack(fill='both', expand=True, padx=10, pady=5)

        # 上部：数据展示区
        data_frame = ttk.LabelFrame(main_pane, text="数据展示区（采集/导入的全部数据）", padding=5)
        main_pane.add(data_frame, weight=3)

        tree_frame = ttk.Frame(data_frame)
        tree_frame.pack(fill='both', expand=True)

        columns = ("编号", "发布者", "内容", "时间", "点赞", "评论")
        self.tree = ttk.Treeview(tree_frame, columns=columns, show='headings', height=15)

        col_widths = {"编号": 50, "发布者": 120, "内容": 350, "时间": 150, "点赞": 200, "评论": 300}
        for col in columns:
            self.tree.heading(col, text=col)
            self.tree.column(col, width=col_widths[col], anchor='w')

        style = ttk.Style()
        style.configure('Treeview', rowheight=45, font=(FONT_NAME, 10))
        style.configure('Treeview.Heading', font=(FONT_NAME, 11, "bold"))

        self.tree.pack(side='left', fill='both', expand=True)

        vsb = ttk.Scrollbar(tree_frame, orient='vertical', command=self.tree.yview)
        vsb.pack(side='right', fill='y')
        self.tree.configure(yscrollcommand=vsb.set)

        # 下部：并列日志区
        logs_frame = ttk.Frame(main_pane)
        main_pane.add(logs_frame, weight=1)

        # 左日志：数据日志
        left_log_frame = ttk.LabelFrame(logs_frame, text="分析结果日志", padding=3)
        left_log_frame.pack(side='left', fill='both', expand=True, padx=3)

        self.data_text = tk.Text(left_log_frame, state='disabled', wrap='word',
                                 font=(FONT_NAME, FONT_SIZE_LOG), height=10)
        self.data_text.pack(fill='both', expand=True)

        # 右日志：系统执行信息
        right_log_frame = ttk.LabelFrame(logs_frame, text="系统执行信息", padding=3)
        right_log_frame.pack(side='left', fill='both', expand=True, padx=3)

        self.sys_text = tk.Text(right_log_frame, state='disabled', wrap='word',
                                font=(FONT_NAME, FONT_SIZE_LOG), height=10)
        self.sys_text.pack(fill='both', expand=True)

        # 底部状态栏
        status_frame = ttk.Frame(self.master)
        status_frame.pack(fill='x', padx=10, pady=5)
        self.status_var = tk.StringVar()
        self.status_var.set("就绪")
        ttk.Label(status_frame, textvariable=self.status_var, font=(FONT_NAME, FONT_SIZE_LABEL),
                  foreground=ACCENT_COLOR).pack(side='left')

    def _schedule_ui_log_flush(self):
        try:
            self.ui_logger.flush_to_widgets()
        except Exception:
            pass
        self.master.after(200, self._schedule_ui_log_flush)

    def _set_buttons_state(self, enabled=True):
        state = 'normal' if enabled else 'disabled'
        for btn in self.master.winfo_children():
            if isinstance(btn, (ttk.Frame, ttk.PanedWindow)):
                self._disable_buttons_recursive(btn, state)

    def _disable_buttons_recursive(self, parent, state):
        for child in parent.winfo_children():
            if isinstance(child, ttk.Button):
                child.configure(state=state)
            elif isinstance(child, (ttk.Frame, ttk.PanedWindow)):
                self._disable_buttons_recursive(child, state)

    def choose_save_path(self):
        fmt = self.combo_format.get() or 'json'
        ft = [('JSON 文件', '*.json')] if fmt == 'json' else [('Excel 文件', '*.xlsx')]
        p = filedialog.asksaveasfilename(defaultextension=f".{fmt}", filetypes=ft, title="选择保存路径")
        if p:
            self.entry_path.delete(0, 'end')
            self.entry_path.insert(0, p)

    def import_file(self):
        p = filedialog.askopenfilename(filetypes=[('JSON', '*.json'), ('Excel', '*.xlsx;*.xls')], title="选择导入文件")
        if not p:
            return
        try:
            if p.lower().endswith('.json'):
                with open(p, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                if isinstance(data, dict) and 'posts' in data:
                    data = data['posts']
                self.all_posts = data if isinstance(data, list) else []
            else:
                df = pd.read_excel(p)
                posts = []
                for _, row in df.iterrows():
                    posts.append({
                        "编号": row.get("编号", ""),
                        "发布者": row.get("发布者", ""),
                        "内容": row.get("内容", ""),
                        "时间": row.get("时间", ""),
                        "点赞": row.get("点赞", "") if "点赞" in row else "",
                        "评论": row.get("评论", "") if "评论" in row else []
                    })
                self.all_posts = posts
            self._refresh_treeview()
            self.ui_logger.log_data(f"已导入文件：{p}，条数：{len(self.all_posts)}")
            self.status_var.set(f"已加载 {len(self.all_posts)} 条数据")
            messagebox.showinfo("导入成功", f"已导入 {len(self.all_posts)} 条数据。")
        except Exception as e:
            messagebox.showerror("导入失败", str(e))
            self.ui_logger.log_sys(f"导入失败：{e}")

    def _refresh_treeview(self):
        for r in self.tree.get_children():
            self.tree.delete(r)
        for row in self.all_posts:
            comments = row.get('评论', [])
            if isinstance(comments, list):
                comments_s = " | ".join([str(x) for x in comments[:3]])
                if len(comments) > 3:
                    comments_s += f"...等 {len(comments) - 3} 条"
            else:
                comments_s = str(comments)
            likes = row.get('点赞', '') or ""
            self.tree.insert('', 'end', values=(
                row.get('编号', ''),
                row.get('发布者', ''),
                row.get('内容', '')[:100],
                format_time_display(row.get('时间', '')),
                likes[:100] if isinstance(likes, str) else "",
                comments_s
            ))

    def start_collect(self):
        try:
            count = int(self.entry_count.get())
            timeout = int(self.entry_timeout.get())
        except Exception:
            messagebox.showerror("参数错误", "采集数量与超时必须为整数。")
            return
        save_path = self.entry_path.get().strip()
        if not save_path:
            messagebox.showerror("路径错误", "请先选择保存路径。")
            return
        self._set_buttons_state(False)
        self.status_var.set("正在采集...")
        self.progress_var.set(0)
        self.ui_logger.log_sys("准备开始采集（后台线程）...")

        def progress_cb(count_now, target):
            try:
                val = min(100, int(count_now / target * 100))
                self.progress_var.set(val)
                self.master.update_idletasks()
            except Exception:
                pass

        def worker():
            try:
                posts = parse_moments_collect(target_count=count, timeout=timeout, progress_callback=progress_cb,
                                              log_sys=self.ui_logger.log_sys, log_data=self.ui_logger.log_data)
                self.all_posts = posts
                fmt = self.combo_format.get()
                if fmt == 'json':
                    with open(save_path, 'w', encoding='utf-8') as f:
                        json.dump(self.all_posts, f, ensure_ascii=False, indent=2)
                else:
                    pd.DataFrame(self.all_posts).to_excel(save_path, index=False)
                self.ui_logger.log_sys(f"采集并保存完成：{save_path}")
                self._refresh_treeview()
                self.ui_logger.log_data(f"已采集 {len(self.all_posts)} 条并保存到 {save_path}")
                self.status_var.set(f"采集完成：{len(self.all_posts)} 条")
            except Exception as e:
                self.ui_logger.log_sys(f"采集异常：{e}")
                messagebox.showerror("采集失败", str(e))
                self.status_var.set("采集失败")
            finally:
                self._set_buttons_state(True)
                self.progress_var.set(0)

        threading.Thread(target=worker, daemon=True).start()

    def start_analyze(self):
        if not self.all_posts:
            messagebox.showwarning("提示", "请先采集或导入数据再进行分析。")
            return
        self._set_buttons_state(False)
        self.status_var.set("正在分析...")
        self.ui_logger.log_sys("分析线程已启动...")

        def worker():
            try:
                self.ui_logger.log_sys("构建互动网络（基于所有互动数据）...")

                # 从发布者列提取数据
                publishers = [post.get('发布者', '') for post in self.all_posts if post.get('发布者', '')]

                # 应用别名映射
                if self.alias_map:
                    publishers = [self.alias_map.get(p, p) for p in publishers]

                G, pub_counts = build_interaction_graph(publishers, all_posts=self.all_posts,
                                                        like_weight=LIKE_WEIGHT,
                                                        comment_weight=COMMENT_WEIGHT,
                                                        alias_map=self.alias_map,
                                                        log_sys=self.ui_logger.log_sys)
                self.graph = G

                analysis = analyze_graph(G, pub_counts, self.all_posts, use_louvain=True,
                                         log_sys=self.ui_logger.log_sys)
                self.analysis = analysis

                # 中文化分析结果展示
                self.ui_logger.log_data("=" * 70)
                self.ui_logger.log_data("【微信朋友圈互动网络分析结果】")
                self.ui_logger.log_data("=" * 70)

                self.ui_logger.log_data("")
                self.ui_logger.log_data("📊 网络基本信息")
                self.ui_logger.log_data("-" * 70)
                self.ui_logger.log_data(f"  参与人数（节点数）：{analysis.get('num_nodes', 0)} 人")
                self.ui_logger.log_data(f"  互动关系总数（边数）：{analysis.get('num_edges', 0)} 条")
                self.ui_logger.log_data(f"  网络密度：{analysis.get('network_density', 0):.4f}")
                self.ui_logger.log_data(f"  平均互动强度：{analysis.get('avg_weight', 0):.2f}")
                self.ui_logger.log_data(f"  最高互动强度：{analysis.get('max_weight', 0):.0f}")

                self.ui_logger.log_data("")
                self.ui_logger.log_data("👥 社交活跃度排行 Top 10（按度中心性）")
                self.ui_logger.log_data("-" * 70)
                for i, (name, val) in enumerate(analysis.get('top_degree', [])[:10], start=1):
                    bar_len = min(50, int(val * 30))
                    bar = "█" * bar_len
                    self.ui_logger.log_data(f"  {i:2d}. {name:20s} 活跃度: {val:.4f} {bar}")

                self.ui_logger.log_data("")
                self.ui_logger.log_data("🌉 网络桥梁人物 Top 10（按介数中心性）")
                self.ui_logger.log_data("-" * 70)
                for i, (name, val) in enumerate(analysis.get('top_betweenness', [])[:10], start=1):
                    bar_len = min(50, int(val * 30))
                    bar = "█" * bar_len
                    self.ui_logger.log_data(f"  {i:2d}. {name:20s} 指数: {val:.4f} {bar}")

                self.ui_logger.log_data("")
                self.ui_logger.log_data("🎯 社区划分结果")
                self.ui_logger.log_data("-" * 70)
                community_groups = analysis.get('community_groups', {})
                if not community_groups:
                    self.ui_logger.log_data("  未能检测到明显社区结构")
                else:
                    sorted_communities = sorted(community_groups.items(),
                                                key=lambda item: len(item[1]), reverse=True)
                    for cid, members in sorted_communities:
                        self.ui_logger.log_data("")
                        self.ui_logger.log_data(f"  社区 {cid + 1} （{len(members)} 人）")
                        members_to_show = members[:10]
                        members_str = "    成员: " + "、".join(members_to_show)
                        if len(members) > 10:
                            members_str += f"等 {len(members) - 10} 人"
                        self.ui_logger.log_data(members_str)

                self.ui_logger.log_data("")
                self.ui_logger.log_data("✅ 分析完成！")
                self.ui_logger.log_data("=" * 70)

                self.status_var.set(
                    f"分析完成：{analysis.get('num_nodes', 0)} 人，{analysis.get('num_edges', 0)} 条关系，{len(community_groups)} 个社区")
                messagebox.showinfo("分析完成",
                                    f"分析已完成：{analysis.get('num_nodes', 0)} 人参与，{analysis.get('num_edges', 0)} 条互动关系，{len(community_groups)} 个社区")
            except Exception as e:
                self.ui_logger.log_sys(f"分析异常：{e}")
                import traceback
                traceback.print_exc()
                messagebox.showerror("分析失败", str(e))
                self.status_var.set("分析失败")
            finally:
                self._set_buttons_state(True)

        threading.Thread(target=worker, daemon=True).start()

    def run_alias_suggestion(self):
        if not self.all_posts:
            messagebox.showwarning("无数据", "请先采集或导入数据。")
            return

        thr = 0.86

        def on_ok():
            nonlocal thr
            try:
                v = float(entry.get())
                if 0 <= v <= 1:
                    thr = v
                else:
                    messagebox.showerror("参数错误", "阈值应在 0-1 之间")
                    return
            except Exception:
                messagebox.showerror("参数错误", "请输入有效的数字")
                return
            dlg.destroy()
            self._do_alias_suggestion(thr)

        dlg = tk.Toplevel(self.master)
        dlg.title("别名阈值设置")
        dlg.geometry("300x150")
        tk.Label(dlg, text="相似度阈值 (0-1，越高越严格)", font=(FONT_NAME, 11)).pack(padx=8, pady=6)
        entry = ttk.Entry(dlg, width=20)
        entry.insert(0, str(thr))
        entry.pack(padx=8, pady=6)
        ttk.Button(dlg, text="确定", command=on_ok).pack(pady=6)

    def _do_alias_suggestion(self, threshold):
        self.ui_logger.log_sys(f"开始从发布者列进行别名聚类（阈值 {threshold}）...")

        def worker():
            try:
                suggestions = suggest_aliases_from_publishers(self.all_posts, threshold=threshold)
                self.last_suggestions = suggestions
                if not suggestions:
                    self.ui_logger.log_sys("未发现满足阈值的相似名称。")
                    messagebox.showinfo("别名建议", "未发现满足阈值的相似名称。")
                    return

                preview = "\n".join([f"{a}  <->  {b}  (相似度: {s:.3f})"
                                     for a, b, s in suggestions[:500]])

                def on_save():
                    p = filedialog.asksaveasfilename(defaultextension=".json",
                                                     filetypes=[("JSON", "*.json")])
                    if not p:
                        return
                    try:
                        with open(p, 'w', encoding='utf-8') as f:
                            json.dump([{"a": a, "b": b, "score": s} for a, b, s in suggestions],
                                      f, ensure_ascii=False, indent=2)
                        messagebox.showinfo("保存成功", f"已保存 {len(suggestions)} 条建议")
                    except Exception as e:
                        messagebox.showerror("保存失败", str(e))

                amap = build_alias_map_from_suggestions(suggestions)
                self._last_auto_alias_map = amap
                self.ui_logger.log_sys(f"自动生成 alias_map（{len(amap)} 项），可点击'应用别名'应用。")

                preview_dlg = tk.Toplevel(self.master)
                preview_dlg.title("别名建议预览")
                preview_dlg.geometry("900x600")
                txt = tk.Text(preview_dlg, wrap='word', font=(FONT_NAME, 10))
                txt.pack(padx=6, pady=6, fill='both', expand=True)
                txt.insert('1.0', preview)
                txt.configure(state='disabled')
                btn_frame = ttk.Frame(preview_dlg)
                btn_frame.pack(pady=6)
                ttk.Button(btn_frame, text="保存建议", command=on_save).grid(row=0, column=0, padx=6)
                ttk.Button(btn_frame, text="关闭", command=preview_dlg.destroy).grid(row=0, column=1, padx=6)
            except Exception as e:
                self.ui_logger.log_sys(f"别名建议异常：{e}")
                messagebox.showerror("别名建议失败", str(e))

        threading.Thread(target=worker, daemon=True).start()

    def apply_alias_map(self):
        amap = getattr(self, '_last_auto_alias_map', None)
        if not amap:
            messagebox.showwarning("无映射", "尚无自动生成的 alias_map，请先运行'别名建议'。")
            return
        if not messagebox.askyesno("确认", f"将应用 {len(amap)} 条别名映射？"):
            return
        self.alias_map.update(amap)
        self.ui_logger.log_sys(f"已应用 alias_map（总映射项数 {len(self.alias_map)}）。")
        messagebox.showinfo("成功", f"已应用 {len(amap)} 条别名映射。")

    def show_network_graph(self):
        """显示互动关系网络图"""
        if not self.graph or not self.analysis:
            messagebox.showwarning("提示", "请先完成分析后再查看关系图。")
            return

        self.ui_logger.log_sys("正在生成关系图...")

        def worker():
            try:
                import tkinter.simpledialog as simpledialog

                # 创建新窗口
                graph_window = tk.Toplevel(self.master)
                graph_window.title("朋友圈互动关系网络图")
                graph_window.geometry("1200x800")

                # 创建控制面板
                control_frame = ttk.Frame(graph_window)
                control_frame.pack(fill='x', padx=10, pady=10)

                ttk.Label(control_frame, text="可视化选项：", font=(FONT_NAME, 11, "bold")).pack(side='left', padx=5)

                layout_var = tk.StringVar(value="spring")
                ttk.Label(control_frame, text="布局：").pack(side='left', padx=5)
                layout_combo = ttk.Combobox(control_frame, textvariable=layout_var,
                                            values=["spring", "circular", "kamada_kawai"],
                                            state="readonly", width=12)
                layout_combo.pack(side='left', padx=2)

                node_size_var = tk.DoubleVar(value=300)
                ttk.Label(control_frame, text="节点大小：").pack(side='left', padx=5)
                ttk.Scale(control_frame, from_=50, to=1000, variable=node_size_var,
                          orient='horizontal', length=150).pack(side='left', padx=2)

                show_labels_var = tk.BooleanVar(value=True)
                ttk.Checkbutton(control_frame, text="显示标签", variable=show_labels_var).pack(side='left', padx=5)

                show_edges_var = tk.BooleanVar(value=True)
                ttk.Checkbutton(control_frame, text="显示连接线", variable=show_edges_var).pack(side='left', padx=5)

                # 添加选择特定人员的功能（多选）
                ttk.Label(control_frame, text="选择人员：").pack(side='left', padx=5)
                
                # 创建一个框架来容纳Listbox和滚动条
                list_frame = ttk.Frame(control_frame)
                list_frame.pack(side='left', padx=2)
                
                # 创建滚动条
                scrollbar = ttk.Scrollbar(list_frame, orient='vertical')
                scrollbar.pack(side='right', fill='y')
                
                # 过滤掉包含'回复'的人员
                all_people = [person for person in sorted(list(self.graph.nodes())) if '回复' not in person]
                
                # 创建Listbox，设置为多选模式，增大宽度和高度
                person_listbox = tk.Listbox(list_frame, yscrollcommand=scrollbar.set,
                                          selectmode='extended', width=25, height=8)
                person_listbox.pack(side='left', fill='both', expand=True)
                
                # 绑定滚动条
                scrollbar.config(command=person_listbox.yview)
                
                # 填充人员列表
                for person in all_people:
                    person_listbox.insert('end', person)

                # 添加全选/取消全选按钮
                def select_all():
                    person_listbox.select_set(0, 'end')
                
                def deselect_all():
                    person_listbox.selection_clear(0, 'end')
                
                select_frame = ttk.Frame(control_frame)
                select_frame.pack(side='left', padx=2)
                
                ttk.Button(select_frame, text="全选", command=select_all, width=5).pack()
                ttk.Button(select_frame, text="取消全选", command=deselect_all, width=7).pack()

                # 添加关系深度选择
                ttk.Label(control_frame, text="关系深度：").pack(side='left', padx=5)
                depth_var = tk.IntVar(value=1)
                depth_combo = ttk.Combobox(control_frame, textvariable=depth_var,
                                          values=[1, 2, 3],
                                          state="readonly", width=5)
                depth_combo.pack(side='left', padx=2)

                def update_graph():
                    plt.close('all')

                    G = self.graph
                    analysis = self.analysis

                    # 处理选择特定人员的情况
                    selected_indices = person_listbox.curselection()
                    if selected_indices:
                        # 获取所有选中的人员
                        selected_people = [person_listbox.get(i) for i in selected_indices]
                        
                        # 获取与选定人员有关系的节点
                        depth = depth_var.get()
                        related_nodes = set()
                        
                        for person in selected_people:
                            related_nodes.add(person)
                            
                            if depth >= 1:
                                # 一级关系
                                for neighbor in G.neighbors(person):
                                    related_nodes.add(neighbor)
                                
                            if depth >= 2:
                                # 二级关系
                                level1 = list(G.neighbors(person))
                                for n in level1:
                                    for neighbor in G.neighbors(n):
                                        related_nodes.add(neighbor)
                                
                            if depth >= 3:
                                # 三级关系
                                level1 = list(G.neighbors(person))
                                for n in level1:
                                    level2 = list(G.neighbors(n))
                                    for neighbor in level2:
                                        if neighbor not in related_nodes:
                                            related_nodes.add(neighbor)
                                        for level3_neighbor in G.neighbors(neighbor):
                                            related_nodes.add(level3_neighbor)
                        
                        # 创建子图
                        G = G.subgraph(related_nodes)
                        
                        # 记录选中的人员用于标题显示
                        selected_person = ', '.join(selected_people[:3])
                        if len(selected_people) > 3:
                            selected_person += f' 等{len(selected_people)}人'
                    else:
                        selected_person = "全部人员"

                    fig, ax = plt.subplots(figsize=(12, 8), dpi=100)
                    fig.patch.set_facecolor('#f5f5f5')

                    # 选择布局
                    layout_type = layout_var.get()
                    if layout_type == "spring":
                        pos = nx.spring_layout(G, k=0.5, iterations=50, seed=42)
                    elif layout_type == "circular":
                        pos = nx.circular_layout(G)
                    else:  # kamada_kawai
                        try:
                            pos = nx.kamada_kawai_layout(G)
                        except:
                            pos = nx.spring_layout(G, k=0.5, iterations=50, seed=42)

                    # 绘制边
                    if show_edges_var.get():
                        # 创建一个仅包含有点赞的边的子图
                        # 评论数据仍然参与计算权重和中心性，但不在关系图中显示
                        edges_with_likes = [(u, v) for u, v, d in G.edges(data=True) if d.get('likes', 0) > 0]
                        
                        # 绘制有点赞的边
                        if edges_with_likes:
                            nx.draw_networkx_edges(G, pos, ax=ax, alpha=0.3, width=1.5,
                                                   edge_color='#999999', edge_cmap=plt.cm.Blues,
                                                   edgelist=edges_with_likes)

                    # 计算节点颜色（根据度中心性）
                    degree_cent = analysis.get('degree_centrality', {})
                    node_colors = [degree_cent.get(node, 0) for node in G.nodes()]

                    # 计算节点大小（根据度）
                    node_size = node_size_var.get()
                    node_sizes = [node_size * (1 + degree_cent.get(node, 0.1)) for node in G.nodes()]

                    # 绘制节点
                    nodes = nx.draw_networkx_nodes(G, pos, ax=ax,
                                                   node_color=node_colors,
                                                   node_size=node_sizes,
                                                   cmap=plt.cm.RdYlGn,
                                                   alpha=0.8,
                                                   vmin=0, vmax=1)

                    # 绘制标签
                    if show_labels_var.get():
                        nx.draw_networkx_labels(G, pos, ax=ax, font_size=8,
                                                font_family=FONT_NAME)

                    # 添加图例和信息
                    info_text = f"""网络统计信息
节点数（人）：{analysis.get('num_nodes', 0)}
边数（关系）：{analysis.get('num_edges', 0)}
网络密度：{analysis.get('network_density', 0):.4f}
平均互动强度：{analysis.get('avg_weight', 0):.2f}"""

                    ax.text(0.02, 0.98, info_text, transform=ax.transAxes,
                            fontsize=10, verticalalignment='top',
                            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8),
                            fontproperties={'family': FONT_NAME, 'size': 9})

                    # 添加颜色条
                    sm = plt.cm.ScalarMappable(cmap=plt.cm.RdYlGn,
                                               norm=plt.Normalize(vmin=0, vmax=1))
                    sm.set_array([])
                    cbar = plt.colorbar(sm, ax=ax, fraction=0.046, pad=0.04)
                    cbar.set_label('度中心性', fontproperties={'family': FONT_NAME, 'size': 9})

                    # 根据是否选择了特定人员来设置标题
                    if selected_person != "全部人员":
                        depth_text = {1: "直接关系", 2: "朋友的朋友", 3: "三级关系"}.get(depth, "关系")
                        ax.set_title(f'{selected_person}的朋友圈{depth_text}网络', fontsize=14,
                                    fontproperties={'family': FONT_NAME, 'size': 12, 'weight': 'bold'})
                    else:
                        ax.set_title('朋友圈互动关系网络', fontsize=14,
                                    fontproperties={'family': FONT_NAME, 'size': 12, 'weight': 'bold'})
                    ax.axis('off')
                    plt.tight_layout()
                    plt.show()

                ttk.Button(control_frame, text="生成图表", command=update_graph).pack(side='left', padx=20)

                # 创建信息展示区
                info_frame = ttk.LabelFrame(graph_window, text="节点详细信息", padding=5)
                info_frame.pack(fill='both', expand=True, padx=10, pady=10)

                # 创建树形视图
                columns = ("节点", "度中心性", "介数中心性", "所属社区", "互动数")
                info_tree = ttk.Treeview(info_frame, columns=columns, show='headings', height=20)

                col_widths = {"节点": 150, "度中心性": 100, "介数中心性": 100, "所属社区": 80, "互动数": 80}
                for col in columns:
                    info_tree.heading(col, text=col)
                    info_tree.column(col, width=col_widths[col], anchor='w')

                # 填充数据
                degree_cent = self.analysis.get('degree_centrality', {})
                betweenness = self.analysis.get('betweenness', {})
                communities = self.analysis.get('communities', {})

                for node in sorted(self.graph.nodes(),
                                   key=lambda x: degree_cent.get(x, 0), reverse=True):
                    degree = self.graph.degree(node)
                    info_tree.insert('', 'end', values=(
                        node,
                        f"{degree_cent.get(node, 0):.4f}",
                        f"{betweenness.get(node, 0):.4f}",
                        f"社区 {communities.get(node, -1) + 1}",
                        f"{degree}"
                    ))

                vsb = ttk.Scrollbar(info_frame, orient='vertical', command=info_tree.yview)
                vsb.pack(side='right', fill='y')
                info_tree.configure(yscrollcommand=vsb.set)
                info_tree.pack(fill='both', expand=True)

                # 导出功能
                export_frame = ttk.Frame(graph_window)
                export_frame.pack(fill='x', padx=10, pady=10)

                def export_graph():
                    save_path = filedialog.asksaveasfilename(
                        defaultextension=".png",
                        filetypes=[("PNG图片", "*.png"), ("PDF", "*.pdf"), ("SVG", "*.svg")]
                    )
                    if save_path:
                        try:
                            plt.savefig(save_path, dpi=300, bbox_inches='tight')
                            messagebox.showinfo("成功", f"关系图已保存到：{save_path}")
                            self.ui_logger.log_sys(f"关系图已导出：{save_path}")
                        except Exception as e:
                            messagebox.showerror("失败", f"导出失败：{e}")

                def export_node_data():
                    save_path = filedialog.asksaveasfilename(
                        defaultextension=".xlsx",
                        filetypes=[("Excel", "*.xlsx"), ("CSV", "*.csv")]
                    )
                    if save_path:
                        try:
                            degree_cent = self.analysis.get('degree_centrality', {})
                            betweenness = self.analysis.get('betweenness', {})
                            communities = self.analysis.get('communities', {})

                            rows = []
                            for node in self.graph.nodes():
                                rows.append({
                                    '节点': node,
                                    '度': self.graph.degree(node),
                                    '度中心性': degree_cent.get(node, 0),
                                    '介数中心性': betweenness.get(node, 0),
                                    '所属社区': communities.get(node, -1) + 1
                                })

                            df = pd.DataFrame(rows)
                            if save_path.endswith('.xlsx'):
                                df.to_excel(save_path, index=False)
                            else:
                                df.to_csv(save_path, index=False, encoding='utf-8')

                            messagebox.showinfo("成功", f"数据已保存到：{save_path}")
                            self.ui_logger.log_sys(f"节点数据已导出：{save_path}")
                        except Exception as e:
                            messagebox.showerror("失败", f"导出失败：{e}")

                ttk.Button(export_frame, text="导出图表(PNG/PDF/SVG)", command=export_graph).pack(side='left', padx=5)
                ttk.Button(export_frame, text="导出节点数据(Excel/CSV)", command=export_node_data).pack(side='left',
                                                                                                        padx=5)

                # 生成初始图表
                update_graph()
                self.ui_logger.log_sys("关系图已生成。")

            except Exception as e:
                self.ui_logger.log_sys(f"生成关系图异常：{e}")
                import traceback
                traceback.print_exc()
                messagebox.showerror("生成失败", str(e))

        threading.Thread(target=worker, daemon=True).start()
    def show_data_interpretation(self):
        """显示软件使用手册"""
        dlg = tk.Toplevel(self.master)
        dlg.title("软件使用手册")
        dlg.geometry("1000x700")
        txt = tk.Text(dlg, wrap='word', font=(FONT_NAME, 11))
        txt.pack(padx=8, pady=8, fill='both', expand=True)
        explanation = """
【微信朋友圈发布者分析工具 - 使用手册】

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
一、核心功能说明
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

本工具通过分析微信朋友圈数据，帮您理解社交网络中的发布者活跃情况和社区结构。

【推荐使用流程】

1️⃣ 获取数据
   - 【开始采集】：自动从微信桌面版采集朋友圈动态
   - 【导入数据】：导入之前保存的 JSON 或 Excel 文件

2️⃣ 数据清理（可选）
   - 【别名建议】：自动发现相似的人名（发布者、点赞者、评论者）
   - 【应用别名】：将相似名称统一为一个人，提高分析准确度

3️⃣ 进行分析
   - 【关系网分析】：分析所有发布者的活跃度和社区分布

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
二、分析结果解读
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

📊 网络基本信息
  • 发布者总数：参与发布朋友圈内容的人数
  • 网络密度：衡量发布者之间的关联紧密程度（0-1）

👥 发布者活跃度排行
  • 按发布数排序，显示谁在朋友圈最活跃
  • 发布数越多，说明该人越喜欢分享

🎯 社区划分结果
  • 自动发现的"朋友圈中的小圈子"
  • 同社区的人发布内容差异度较小（可能是同一类型朋友）
  • 不同社区的发布者风格差异较大

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
三、常见问题解答
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Q: 为什么同一个人出现了多个名字？
A: 微信中可能存在备注差异。使用"别名建议"功能自动识别，
   设置合适的相似度阈值（通常 0.85-0.90 较好），然后应用。

Q: 什么是"网络密度"？
A: 0-1 的数值，越接近 1 说明发布者之间的关联越紧密，
   越接近 0 说明发布者相对独立。

Q: 社区划分的依据是什么？
A: 基于发布者在朋友圈的活动模式相似性自动分组，
   同社区成员的发布时间、频率、类型等相似。

Q: 如何导出分析结果？
A: 分析完成后，所有结果会显示在左侧"分析结果日志"框中。
   您可以直接从界面复制或截图保存。

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
四、隐私与合规提示
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

⚠️ 本工具仅分析您有权访问的数据
⚠️ 请勿在未经授权的情况下传播或公开发布涉及他人的信息
⚠️ 请遵守当地法律法规及微信平台的使用规定

Power:PGX Time:25.10.11 Verson:4.0
"""
        txt.insert('1.0', explanation)
        txt.configure(state='disabled')

def main():
    root = tk.Tk()
    app = MomentsApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()