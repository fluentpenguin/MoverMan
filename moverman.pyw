#!/usr/bin/env python3
"""
moverman 2.0 - copy, move and compare files between folders and drives (Windows 11)

MOVE     Copy files from one or more sources to a target.
         "Move, Don't Copy" (off by default) deletes each source file ONLY after the
         copy has been verified byte-for-byte (SHA-256).
COMPARE  Lists the files in source A that are missing from up to 4 targets (B-E).

Run:   double-click moverman.pyw   (or:  python moverman.pyw)
Needs: Python 3.8+ for Windows (tkinter is included in the standard installer).
License: MIT
"""
import errno
import hashlib
import os
import queue
import shutil
import stat
import string
import threading
import time
import tkinter as tk
from pathlib import Path
from tkinter import filedialog, messagebox, ttk

__version__ = "2.0.0"

CHUNK = 8 * 1024 * 1024                      # read/write block size
PART = ".moverman_part"                      # suffix of in-progress files
STAGING = Path.home() / "Downloads" / "moverman_temp"
SKIP_DIRS = {"system volume information", "$recycle.bin"}
FATAL = {"E115", "E119"}                     # errors that stop the whole run
DISPLAY_LIMIT = 2000                         # max missing files shown per target

ERRORS = {
    "E100": "No valid source selected",
    "E101": "No valid target selected",
    "E102": "Source and target overlap (one is inside the other)",
    "E103": "Not enough free space",
    "E104": "Two selected sources overlap",
    "E110": "Could not read a source file",
    "E111": "Could not write to the target",
    "E112": "Size mismatch after copying",
    "E113": "Verification failed (checksum mismatch) - source kept",
    "E114": "Permission denied",
    "E115": "Disk is full",
    "E116": "Path is too long",
    "E117": "File is in use by another program",
    "E118": "File or folder not found",
    "E119": "Drive disconnected or I/O error",
    "E120": "Copied and verified, but the source file could not be deleted",
    "E130": "Cancelled by user",
    "E140": "Could not read a folder while scanning",
    "E150": "Could not save the file",
    "E199": "Unexpected error",
}


# ----------------------------------------------------------------- helpers
class Cancelled(Exception):
    pass


class MoverError(Exception):
    def __init__(self, code, detail=""):
        super().__init__(detail)
        self.code, self.detail = code, detail

    def __str__(self):
        text = f"[{self.code}] {ERRORS.get(self.code, 'Error')}"
        return f"{text}: {self.detail}" if self.detail else text


def lp(p):
    """Windows long-path safe form."""
    p = os.path.abspath(str(p))
    if os.name == "nt" and not p.startswith("\\\\?\\"):
        return ("\\\\?\\UNC\\" + p[2:]) if p.startswith("\\\\") else "\\\\?\\" + p
    return p


def show(p):
    p = str(p)
    if p.startswith("\\\\?\\UNC\\"):
        return "\\\\" + p[8:]
    return p[4:] if p.startswith("\\\\?\\") else p


def as_error(exc, default="E199", path=""):
    if isinstance(exc, MoverError):
        return exc
    win, err = getattr(exc, "winerror", None), getattr(exc, "errno", None)
    if err == errno.ENOSPC or win == 112:
        code = "E115"
    elif win in (32, 33):
        code = "E117"
    elif win == 206 or err == errno.ENAMETOOLONG:
        code = "E116"
    elif win in (21, 55, 59, 64, 121, 1117, 1393):
        code = "E119"
    elif isinstance(exc, PermissionError):
        code = "E114"
    elif isinstance(exc, FileNotFoundError):
        code = "E118"
    else:
        code = default
    reason = getattr(exc, "strerror", None) or str(exc)
    return MoverError(code, f"{show(path)} ({reason})" if path else reason)


def fmt_size(n):
    n = float(n)
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024:
            return f"{n:,.0f} {unit}" if unit == "B" else f"{n:,.1f} {unit}"
        n /= 1024
    return f"{n:,.2f} TB"


def fmt_speed(bps):
    return f"{bps / 1048576:,.1f} MB/s"


def fmt_time(sec):
    if sec is None:
        return "calculating..."
    h, rem = divmod(int(sec), 3600)
    m, s = divmod(rem, 60)
    return f"{h}:{m:02d}:{s:02d}"


def inside(child, parent):
    c = os.path.normcase(os.path.realpath(child))
    p = os.path.normcase(os.path.realpath(parent))
    return c == p or c.startswith(p.rstrip(os.sep) + os.sep)


def source_base(path):
    path = os.path.normpath(path)
    name = os.path.basename(path)
    if name:
        return name
    drive = os.path.splitdrive(path)[0].replace(":", "")
    return f"Drive_{drive}" if drive else "Drive"


def dest_rel(source, rel):
    if os.path.isfile(lp(source)):
        return rel
    return os.path.join(source_base(source), rel)


def unique(path):
    base, ext = os.path.splitext(path)
    n = 2
    while os.path.exists(f"{base} ({n}){ext}"):
        n += 1
    return f"{base} ({n}){ext}"


def list_drives():
    out = []
    if os.name == "nt":
        for c in string.ascii_uppercase:
            d = f"{c}:\\"
            if os.path.exists(d):
                try:
                    u = shutil.disk_usage(d)
                    out.append((d, f"{d}    {fmt_size(u.free)} free of {fmt_size(u.total)}"))
                except OSError:
                    out.append((d, d))
    else:
        out.append(("/", "/"))
    return out


def keep_awake(on):
    """Stop Windows sleeping during a long job (call from the worker thread)."""
    if os.name == "nt":
        try:
            import ctypes
            ctypes.windll.kernel32.SetThreadExecutionState(0x80000000 | (0x1 if on else 0))
        except Exception:
            pass


def enable_dpi():
    if os.name == "nt":
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass


# ----------------------------------------------------------------- engine
class Tracker:
    """Progress, speed (smoothed) and time-left for a job."""

    def __init__(self, total=0, factor=1):
        self.total, self.factor, self.done, self.label = total, max(1, factor), 0.0, ""
        self.t0 = self._t = time.monotonic()
        self._d, self.speed = 0.0, 0.0

    def add(self, n):
        self.done += n / self.factor
        return self.snapshot()

    def finish(self):
        self.total = self.done = max(self.total, self.done)
        return self.snapshot(True)

    def snapshot(self, force=False):
        now = time.monotonic()
        dt = now - self._t
        if not force and dt < 0.4:
            return None
        if dt >= 0.2:
            inst = (self.done - self._d) / dt
            self.speed = inst if self.speed == 0 else 0.7 * self.speed + 0.3 * inst
            self._t, self._d = now, self.done
        pct = min(100.0, self.done * 100 / self.total) if self.total > 0 else None
        eta = max(0.0, (self.total - self.done) / self.speed) if self.total > 0 and self.speed > 1 else None
        return dict(pct=pct, done=self.done, total=self.total, speed=self.speed,
                    eta=eta, elapsed=now - self.t0, label=self.label)


def scan(path, cancel, errors, on_file=None):
    """Read-only walk. Returns [(abs_path, rel_path_from_root, size)]."""
    out = []
    root = lp(path)
    if os.path.isfile(root):
        size = os.path.getsize(root)
        if on_file:
            on_file(size)
        return [(root, os.path.basename(path), size)]

    def onerr(e):
        errors.append(as_error(e, "E140", getattr(e, "filename", "") or path))

    for d, dirs, files in os.walk(root, onerror=onerr):
        if cancel.is_set():
            raise Cancelled()
        dirs[:] = [x for x in dirs if x.lower() not in SKIP_DIRS]
        for n in files:
            p = os.path.join(d, n)
            try:
                size = os.path.getsize(p)
            except OSError as e:
                errors.append(as_error(e, "E140", p))
                continue
            out.append((p, os.path.relpath(p, root), size))
            if on_file:
                on_file(size)
    return out


def hash_file(path, cancel, progress):
    h = hashlib.sha256()
    try:
        with open(path, "rb") as f:
            while True:
                if cancel.is_set():
                    raise Cancelled()
                b = f.read(CHUNK)
                if not b:
                    break
                h.update(b)
                progress(len(b))
    except OSError as e:
        raise as_error(e, "E110", path)
    return h.hexdigest()


def copy_file(src, dst, cancel, progress, hasher=None):
    """Copy via a .part file, check size, then rename. Only READS src."""
    part, ok = dst + PART, False
    try:
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        try:
            fi = open(src, "rb")
        except OSError as e:
            raise as_error(e, "E110", src)
        with fi:
            try:
                fo = open(part, "wb")
            except OSError as e:
                raise as_error(e, "E111", dst)
            with fo:
                while True:
                    if cancel.is_set():
                        raise Cancelled()
                    try:
                        b = fi.read(CHUNK)
                    except OSError as e:
                        raise as_error(e, "E110", src)
                    if not b:
                        break
                    if hasher:
                        hasher.update(b)
                    try:
                        fo.write(b)
                    except OSError as e:
                        raise as_error(e, "E111", dst)
                    progress(len(b))
        if os.path.getsize(part) != os.path.getsize(src):
            raise MoverError("E112", show(src))
        os.replace(part, dst)
        ok = True
    finally:
        if not ok:
            try:
                os.remove(part)
            except OSError:
                pass
    try:
        shutil.copystat(src, dst)
    except OSError:
        pass


def delete_source(path):
    try:
        try:
            os.remove(path)
        except PermissionError:
            os.chmod(path, stat.S_IWRITE)
            os.remove(path)
    except OSError as e:
        raise MoverError("E120", f"{show(path)} ({e.strerror or e})")


def remove_empty_dirs(root):
    for d, _, _ in os.walk(lp(root), topdown=False):
        try:
            os.rmdir(d)          # only succeeds on EMPTY folders
        except OSError:
            pass


def summarize_errors(errors):
    counts = {}
    for e in errors:
        counts[e.code] = counts.get(e.code, 0) + 1
    return ",  ".join(f"{c} x{n}" for c, n in sorted(counts.items()))


# ----------------------------------------------------------------- widgets
def setup_style(root):
    st = ttk.Style(root)
    for theme in ("vista", "clam"):
        if theme in st.theme_names():
            st.theme_use(theme)
            break
    st.configure("Title.TLabel", font=("Segoe UI", 24, "bold"))
    st.configure("Head.TLabel", font=("Segoe UI", 15, "bold"))
    st.configure("Big.TLabel", font=("Segoe UI", 11, "bold"))
    st.configure("Sub.TLabel", foreground="#666666")
    st.configure("Danger.TLabel", foreground="#b00020")
    st.configure("Mode.TButton", font=("Segoe UI", 14, "bold"), padding=(10, 16))


def save_text(parent, default, text):
    path = filedialog.asksaveasfilename(parent=parent, defaultextension=".txt", initialfile=default,
                                        filetypes=[("Text file", "*.txt"), ("All files", "*.*")])
    if not path:
        return
    try:
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
    except OSError as e:
        messagebox.showerror("moverman - E150", str(as_error(e, "E150", path)), parent=parent)


def show_error_codes(parent):
    w = tk.Toplevel(parent)
    w.title("moverman - error codes")
    w.geometry("560x460")
    t = tk.Text(w, wrap="word", font=("Consolas", 10), padx=10, pady=10)
    t.pack(fill="both", expand=True)
    t.insert("end", "\n".join(f"{c}   {m}" for c, m in ERRORS.items()))
    t.config(state="disabled")


def choose_drive(parent):
    drives = list_drives()
    dlg = tk.Toplevel(parent)
    dlg.title("Choose a drive")
    dlg.transient(parent)
    dlg.grab_set()
    lb = tk.Listbox(dlg, width=52, height=min(10, max(3, len(drives))), activestyle="none")
    lb.pack(padx=12, pady=12)
    for _, label in drives:
        lb.insert("end", label)
    result = {"path": None}

    def ok(*_):
        sel = lb.curselection()
        if sel:
            result["path"] = drives[sel[0]][0]
            dlg.destroy()

    lb.bind("<Double-Button-1>", ok)
    row = ttk.Frame(dlg)
    row.pack(pady=(0, 12))
    ttk.Button(row, text="Choose", command=ok).pack(side="left", padx=4)
    ttk.Button(row, text="Cancel", command=dlg.destroy).pack(side="left", padx=4)
    dlg.wait_window()
    return result["path"]


class PathList(ttk.LabelFrame):
    """A list of folders / files / drives."""

    def __init__(self, master, title, max_items=None):
        super().__init__(master, text=title, padding=8)
        self.items, self.max_items = [], max_items
        top = ttk.Frame(self)
        top.pack(fill="both", expand=True)
        self.lb = tk.Listbox(top, height=3, selectmode="extended", activestyle="none", exportselection=False)
        sb = ttk.Scrollbar(top, command=self.lb.yview)
        self.lb.config(yscrollcommand=sb.set)
        self.lb.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        bar = ttk.Frame(self)
        bar.pack(fill="x", pady=(6, 0))
        for text, cmd in (("+ Folder", self.add_folder), ("+ File", self.add_file), ("+ Drive", self.add_drive),
                          ("Remove", self.remove), ("Clear", self.clear)):
            ttk.Button(bar, text=text, command=cmd).pack(side="left", padx=(0, 6))
        self.counter = ttk.Label(bar, style="Sub.TLabel")
        self.counter.pack(side="right")
        self._count()

    def _count(self):
        self.counter.config(text=f"{len(self.items)} selected" + (f" / {self.max_items} max" if self.max_items else ""))

    def add(self, p):
        if not p:
            return
        p = os.path.normpath(p)
        if any(os.path.normcase(p) == os.path.normcase(x) for x in self.items):
            return
        if self.max_items and len(self.items) >= self.max_items:
            messagebox.showinfo("moverman", f"You can add up to {self.max_items} here.", parent=self)
            return
        self.items.append(p)
        self.lb.insert("end", p)
        self._count()

    def add_folder(self):
        self.add(filedialog.askdirectory(parent=self))

    def add_file(self):
        self.add(filedialog.askopenfilename(parent=self))

    def add_drive(self):
        self.add(choose_drive(self))

    def remove(self):
        for i in reversed(self.lb.curselection()):
            self.lb.delete(i)
            del self.items[i]
        self._count()

    def clear(self):
        self.lb.delete(0, "end")
        self.items.clear()
        self._count()


class PathEntry(ttk.LabelFrame):
    """A single folder / file / drive."""

    def __init__(self, master, title, files=False):
        super().__init__(master, text=title, padding=8)
        self.var = tk.StringVar()
        self.columnconfigure(0, weight=1)
        ttk.Entry(self, textvariable=self.var).grid(row=0, column=0, sticky="ew", padx=(0, 6))
        ttk.Button(self, text="Folder", command=lambda: self.var.set(filedialog.askdirectory(parent=self) or self.var.get())).grid(row=0, column=1, padx=2)
        if files:
            ttk.Button(self, text="File", command=lambda: self.var.set(filedialog.askopenfilename(parent=self) or self.var.get())).grid(row=0, column=2, padx=2)
        ttk.Button(self, text="Drive", command=lambda: self.var.set(choose_drive(self) or self.var.get())).grid(row=0, column=3, padx=2)

    def get(self):
        v = self.var.get().strip()
        return os.path.normpath(v) if v else ""


class RunPanel(ttk.Frame):
    """Progress bar, GB done, MB/s, time left and a log."""

    def __init__(self, master):
        super().__init__(master)
        self.bar = ttk.Progressbar(self, maximum=100)
        self.bar.pack(fill="x")
        self.l1 = ttk.Label(self, text="Ready", style="Big.TLabel")
        self.l1.pack(anchor="w", pady=(6, 0))
        self.l2 = ttk.Label(self, text=" ", style="Sub.TLabel")
        self.l2.pack(anchor="w")
        box = ttk.Frame(self)
        box.pack(fill="both", expand=True, pady=(6, 0))
        self.text = tk.Text(box, height=8, wrap="word", state="disabled", font=("Consolas", 9),
                            relief="flat", highlightthickness=1, highlightbackground="#c8c8c8")
        sb = ttk.Scrollbar(box, command=self.text.yview)
        self.text.config(yscrollcommand=sb.set)
        self.text.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.text.tag_config("hd", font=("Consolas", 9, "bold"))
        self.text.tag_config("ok", foreground="#1a7f37")
        self.text.tag_config("err", foreground="#b00020")
        self.text.tag_config("warn", foreground="#b36b00")
        self.text.tag_config("dim", foreground="#6b6b6b")

    def reset(self):
        self.bar["value"] = 0
        self.l1.config(text="Starting...")
        self.l2.config(text=" ")
        self.text.config(state="normal")
        self.text.delete("1.0", "end")
        self.text.config(state="disabled")

    def add(self, text, tag=""):
        self.text.config(state="normal")
        self.text.insert("end", text + "\n", tag)
        self.text.see("end")
        self.text.config(state="disabled")

    def status(self, text):
        self.l1.config(text=text)

    def show(self, s):
        self.bar["value"] = s["pct"] or 0
        total = f" of {fmt_size(s['total'])}" if s["total"] else ""
        pct = f"  ({s['pct']:.1f}%)" if s["pct"] is not None else ""
        label = f"      {s['label']}" if s["label"] else ""
        self.l1.config(text=f"{fmt_size(s['done'])}{total}{pct}{label}")
        self.l2.config(text=f"Speed: {fmt_speed(s['speed'])}      Time left: {fmt_time(s['eta'])}"
                            f"      Elapsed: {fmt_time(s['elapsed'])}")

    def get_text(self):
        return self.text.get("1.0", "end")


# ----------------------------------------------------------------- windows
class ModeWindow(tk.Toplevel):
    TITLE = ""
    GEOMETRY = "780x700"

    def __init__(self, launcher):
        super().__init__(launcher)
        self.launcher = launcher
        self.title(f"moverman - {self.TITLE}")
        self.geometry(self.GEOMETRY)
        self.minsize(720, 620)
        self.q, self.cancel, self.worker, self.run_buttons = queue.Queue(), threading.Event(), None, []
        self.protocol("WM_DELETE_WINDOW", self.close)
        root = ttk.Frame(self, padding=(14, 10))
        root.pack(fill="both", expand=True)
        head = ttk.Frame(root)
        head.pack(fill="x")
        ttk.Button(head, text="< Back", command=self.close).pack(side="left")
        ttk.Label(head, text=self.TITLE, style="Head.TLabel").pack(side="left", padx=12)
        ttk.Button(head, text="Error codes", command=lambda: show_error_codes(self)).pack(side="right")
        self.controls = ttk.Frame(root)
        self.controls.pack(fill="x", pady=(8, 0))
        self.actions = ttk.Frame(root)
        self.actions.pack(fill="x", pady=8)
        self.panel = RunPanel(root)
        self.panel.pack(fill="both", expand=True)
        self.build_controls(self.controls)
        self.build_actions()
        self.btn_stop = ttk.Button(self.actions, text="Stop", state="disabled", command=self.stop)
        self.btn_stop.pack(side="left", padx=(0, 6))
        ttk.Button(self.actions, text="Save log", command=lambda: save_text(
            self, f"moverman_{self.TITLE.lower()}_log.txt", self.panel.get_text())).pack(side="right")
        self.after(100, self.pump)

    # -- helpers used by subclasses
    def add_action(self, text, command, runs=True, side="left"):
        b = ttk.Button(self.actions, text=text, command=command)
        b.pack(side=side, padx=(0, 6))
        if runs:
            self.run_buttons.append(b)
        return b

    def say(self, text, tag=""):
        self.q.put(("log", text, tag))

    def prog(self, snap):
        if snap:
            self.q.put(("prog", snap))

    def status(self, text):
        self.q.put(("status", text))

    def counter(self, prefix):
        state = {"n": 0, "t": 0.0}

        def cb(size):
            state["n"] += 1
            now = time.monotonic()
            if now - state["t"] > 0.25:
                state["t"] = now
                self.status(f"{prefix}... {state['n']:,} files")
        return cb

    def error_box(self, err):
        messagebox.showerror(f"moverman - {err.code}", str(err), parent=self)

    # -- job plumbing
    def start_job(self, fn, *args):
        self.cancel.clear()
        self.panel.reset()
        for b in self.run_buttons:
            b.config(state="disabled")
        self.btn_stop.config(state="normal")
        self.worker = threading.Thread(target=self._run, args=(fn, args), daemon=True)
        self.worker.start()

    def _run(self, fn, args):
        keep_awake(True)
        try:
            fn(*args)
        except Cancelled:
            self.say("Cancelled by user.  [E130]", "warn")
        except MoverError as e:
            self.say(f"X {e}", "err")
        except Exception as e:
            self.say(f"X [E199] {ERRORS['E199']}: {e!r}", "err")
        finally:
            keep_awake(False)
            self.q.put(("done",))

    def stop(self):
        self.cancel.set()
        self.btn_stop.config(state="disabled")
        self.say("Stopping... finishing the current step.", "dim")

    def pump(self):
        try:
            while True:
                m = self.q.get_nowait()
                if m[0] == "log":
                    self.panel.add(m[1], m[2])
                elif m[0] == "prog":
                    self.panel.show(m[1])
                elif m[0] == "status":
                    self.panel.status(m[1])
                elif m[0] == "done":
                    for b in self.run_buttons:
                        b.config(state="normal")
                    self.btn_stop.config(state="disabled")
        except queue.Empty:
            pass
        except tk.TclError:
            return
        try:
            self.after(100, self.pump)
        except tk.TclError:
            pass

    def close(self):
        if self.worker and self.worker.is_alive():
            if not messagebox.askyesno("moverman", "A job is still running. Stop it and go back?", parent=self):
                return
            self.cancel.set()
        self.launcher.deiconify()
        self.destroy()

    def build_controls(self, parent):
        raise NotImplementedError

    def build_actions(self):
        raise NotImplementedError


class MoveWindow(ModeWindow):
    TITLE = "Move"

    def build_controls(self, p):
        self.sources = PathList(p, "Sources - copied FROM (folders, files or drives)")
        self.sources.pack(fill="x")
        self.target = PathEntry(p, "Target - copied TO (e.g. your HDD)")
        self.target.pack(fill="x", pady=(8, 0))
        opt = ttk.LabelFrame(p, text="Options", padding=8)
        opt.pack(fill="x", pady=(8, 0))
        self.v_prevent, self.v_via, self.v_move = tk.BooleanVar(value=True), tk.BooleanVar(value=False), tk.BooleanVar(value=False)
        ttk.Checkbutton(opt, text="Prevent copies - skip files already on the target (same name + size, any folder)",
                        variable=self.v_prevent).pack(anchor="w")
        ttk.Checkbutton(opt, text="Copy via Downloads - one file at a time, temp copy removed automatically",
                        variable=self.v_via).pack(anchor="w")
        ttk.Checkbutton(opt, text="Move, Don't Copy", variable=self.v_move, command=self.move_toggled).pack(anchor="w", pady=(4, 0))
        self.move_note = ttk.Label(opt, text="", style="Danger.TLabel")
        self.move_note.pack(anchor="w", padx=(24, 0))

    def build_actions(self):
        self.add_action("Scan", lambda: self.begin(True))
        self.add_action("Start", lambda: self.begin(False))
        self.add_action("Open target", self.open_target, runs=False)

    def move_toggled(self):
        self.move_note.config(text="Each source file is deleted ONLY after its copy is verified (SHA-256). "
                                   "Skipped duplicates are never deleted." if self.v_move.get() else "")

    def open_target(self):
        t = self.target.get()
        if t and os.path.isdir(t) and hasattr(os, "startfile"):
            os.startfile(t)

    def validate(self, sources, target):
        if not sources:
            raise MoverError("E100", "Add at least one source folder, file or drive.")
        for s in sources:
            if not os.path.exists(s):
                raise MoverError("E100", f"Not found: {s}")
        if not target or not os.path.isdir(target):
            raise MoverError("E101", "Pick an existing target folder or drive.")
        for s in sources:
            if inside(target, s) or inside(s, target):
                raise MoverError("E102", f"{s}  <->  {target}")
        for i, a in enumerate(sources):
            for b in sources[i + 1:]:
                if inside(a, b) or inside(b, a):
                    raise MoverError("E104", f"{a}  <->  {b}")
        if self.v_via.get():
            for s in sources:
                if inside(str(STAGING), s):
                    raise MoverError("E102", f"The Downloads temp folder is inside {s}")

    def begin(self, dry):
        sources, target = list(self.sources.items), self.target.get()
        try:
            self.validate(sources, target)
        except MoverError as e:
            return self.error_box(e)
        if not dry and self.v_move.get():
            if not messagebox.askyesno(
                    "Move, Don't Copy",
                    "Source files will be DELETED after each file is copied and verified.\n\n"
                    "If a source is inside OneDrive, the deletion also syncs to OneDrive's cloud "
                    "(files go to its recycle bin).\n\nContinue?",
                    icon="warning", default="no", parent=self):
                return
        self.start_job(self.job, sources, target, dry, self.v_via.get(), self.v_prevent.get(), self.v_move.get())

    def job(self, sources, target, dry, via, prevent, move):
        cancel, errors, t0 = self.cancel, [], time.monotonic()
        seen = set()
        if prevent:
            self.say("Indexing target...", "dim")
            for p, rel, size in scan(target, cancel, errors, self.counter("Indexing target")):
                if not p.endswith(PART):
                    seen.add((os.path.basename(p).lower(), size))
            self.say(f"Target already holds {len(seen):,} files.", "dim")
        files = []
        for s in sources:
            self.say(f"Scanning {s}", "dim")
            for p, rel, size in scan(s, cancel, errors, self.counter("Scanning")):
                if not p.endswith(PART):
                    files.append((p, dest_rel(s, rel), size))
        todo, skipped = [], 0
        for p, rel, size in files:
            key = (os.path.basename(rel).lower(), size)
            if prevent:
                if key in seen:
                    skipped += 1
                    continue
                seen.add(key)            # also blocks duplicates inside the sources
            todo.append((p, rel, size))
        total = sum(t[2] for t in todo)
        verb = "move" if move else "copy"
        self.say(f"Found {len(files):,} files ({fmt_size(sum(f[2] for f in files))}).", "hd")
        self.say(f"To {verb}: {len(todo):,} files ({fmt_size(total)})   |   "
                 f"Skipped, already on target: {skipped:,}")
        try:
            free = shutil.disk_usage(target).free
            self.say(f"Free space on target: {fmt_size(free)}")
            if total > free:
                self.say(f"! [E103] {ERRORS['E103']}: need {fmt_size(total)}, target has {fmt_size(free)}.", "warn")
            if via and todo:
                dl_free = shutil.disk_usage(str(Path.home())).free
                if max(t[2] for t in todo) > dl_free:
                    self.say("! [E103] Not enough space in Downloads for the largest file.", "warn")
        except OSError:
            pass
        if dry:
            self.report_errors(errors)
            self.say("Scan complete - nothing was copied.", "ok")
            return

        tracker = Tracker(total, factor=1 + (1 if via else 0) + (1 if move else 0))

        def progress(n):
            self.prog(tracker.add(n))

        copied = deleted = 0
        stopped = False
        for i, (src, rel, size) in enumerate(todo, 1):
            if cancel.is_set():
                stopped = True
                break
            tracker.label = f"File {i:,} of {len(todo):,}"
            self.say(f"[{i}/{len(todo)}] {rel}")
            dst = lp(os.path.join(target, rel))
            if os.path.exists(dst):
                dst = unique(dst)
            tmp = None
            hasher = hashlib.sha256() if move else None
            try:
                if via:
                    tmp = lp(STAGING / f"{i}_{os.path.basename(rel)}")
                    copy_file(src, tmp, cancel, progress, hasher)      # source -> Downloads
                    copy_file(tmp, dst, cancel, progress)              # Downloads -> target
                else:
                    copy_file(src, dst, cancel, progress, hasher)
                copied += 1
                if move:
                    if os.path.getsize(dst) != os.path.getsize(src):
                        raise MoverError("E112", show(dst))
                    if hash_file(dst, cancel, progress) != hasher.hexdigest():
                        try:
                            os.remove(dst)
                        except OSError:
                            pass
                        raise MoverError("E113", show(src))
                    delete_source(src)
                    deleted += 1
            except Cancelled:
                stopped = True
                break
            except Exception as e:
                err = as_error(e, "E199", src)
                errors.append(err)
                self.say(f"   X {err}", "err")
                if err.code in FATAL:
                    self.say("Stopping: this error will affect every remaining file.", "err")
                    stopped = True
                    break
            finally:
                if tmp and os.path.exists(tmp):          # our own temp file, never the source
                    try:
                        os.remove(tmp)
                    except OSError:
                        pass
            self.prog(tracker.snapshot(True))
        if via:
            try:
                os.rmdir(STAGING)
            except OSError:
                pass
        if move and not stopped:
            for s in sources:
                if os.path.isdir(lp(s)):
                    remove_empty_dirs(s)
        if not stopped:
            self.prog(tracker.finish())
        elapsed = time.monotonic() - t0
        self.say("", "")
        self.say("--------------- Summary ---------------", "hd")
        self.say(f"{'Moved' if move else 'Copied'}: {copied:,} files   |   Skipped: {skipped:,}"
                 + (f"   |   Source files deleted: {deleted:,}" if move else ""), "ok")
        self.say(f"Time: {fmt_time(elapsed)}   |   Average: {fmt_speed(total / elapsed if elapsed else 0)}")
        if stopped:
            self.say("Stopped before finishing. Run again to continue - finished files are skipped.", "warn")
        self.report_errors(errors)
        if not errors and not stopped:
            self.say("Done - no errors.", "ok")

    def report_errors(self, errors):
        if not errors:
            return
        for e in errors[:25]:
            self.say(f"X {e}", "err")
        if len(errors) > 25:
            self.say(f"... and {len(errors) - 25} more errors (see Save log).", "err")
        self.say(f"Errors: {len(errors)}   ({summarize_errors(errors)})", "err")
        self.say("Files with errors were NOT deleted from the source.", "warn")


class CompareWindow(ModeWindow):
    TITLE = "Compare"

    def build_controls(self, p):
        self.source = PathEntry(p, "Source - device A", files=True)
        self.source.pack(fill="x")
        self.targets = PathList(p, "Targets - B, C, D, E (up to 4)", max_items=4)
        self.targets.pack(fill="x", pady=(8, 0))
        opt = ttk.LabelFrame(p, text="Options", padding=8)
        opt.pack(fill="x", pady=(8, 0))
        self.v_mode, self.v_deep = tk.StringVar(value="name"), tk.BooleanVar(value=False)
        ttk.Radiobutton(opt, text="Match by name + size, anywhere in the target", variable=self.v_mode, value="name").pack(anchor="w")
        ttk.Radiobutton(opt, text="Match by same relative path + size", variable=self.v_mode, value="path").pack(anchor="w")
        ttk.Checkbutton(opt, text="Verify contents (SHA-256) of matched files - slower, catches corrupted copies",
                        variable=self.v_deep).pack(anchor="w", pady=(4, 0))
        self.report = ""

    def build_actions(self):
        self.add_action("Compare", self.begin)
        self.add_action("Save report", lambda: save_text(self, "moverman_missing_files.txt", self.report or "No report yet."),
                        runs=False, side="right")

    def begin(self):
        source, targets = self.source.get(), list(self.targets.items)
        try:
            if not source or not os.path.exists(source):
                raise MoverError("E100", "Pick a source (A).")
            if not targets:
                raise MoverError("E101", "Add at least one target.")
            for t in targets:
                if not os.path.exists(t):
                    raise MoverError("E101", f"Not found: {t}")
                if os.path.normcase(os.path.realpath(t)) == os.path.normcase(os.path.realpath(source)):
                    raise MoverError("E102", f"{t} is the same as the source.")
        except MoverError as e:
            return self.error_box(e)
        self.start_job(self.job, source, targets, self.v_mode.get() == "path", self.v_deep.get())

    def job(self, source, targets, by_path, deep):
        cancel, errors, report, t0 = self.cancel, [], [], time.monotonic()
        letters = "BCDE"

        def key(rel, size):
            return ((rel if by_path else os.path.basename(rel)).lower(), size)

        def out(text, tag="", display=True):
            report.append(text)
            if display:
                self.say(text, tag)

        tr = Tracker(total=0)
        cnt = {"n": 0}

        def cb(size):
            cnt["n"] += 1
            tr.label = f"A: {cnt['n']:,} files"
            self.prog(tr.add(size))

        self.status("Scanning source (A)...")
        src = [x for x in scan(source, cancel, errors, cb) if not x[0].endswith(PART)]
        src_bytes = sum(x[2] for x in src)
        out(f"A (source): {source}   |   {len(src):,} files, {fmt_size(src_bytes)}", "hd")

        tr = Tracker(total=max(src_bytes, 1) * len(targets))
        results = []
        for i, t in enumerate(targets):
            L = letters[i]
            self.status(f"Scanning target {L}...")
            cnt = {"n": 0}

            def cb(size, L=L, cnt=cnt):
                cnt["n"] += 1
                tr.label = f"{L}: {cnt['n']:,} files"
                self.prog(tr.add(size))

            tfiles = [x for x in scan(t, cancel, errors, cb) if not x[0].endswith(PART)]
            index = {}
            for p, rel, size in tfiles:
                index.setdefault(key(rel, size), []).append(p)
            missing, matched = [], []
            for p, rel, size in src:
                k = key(rel, size)
                if k in index:
                    matched.append((p, index[k][0], rel, size))
                else:
                    missing.append((rel, size))
            missing.sort(key=lambda x: x[0].lower())
            results.append(dict(letter=L, path=t, count=len(tfiles), missing=missing, matched=matched, diff=[]))

        if deep and any(r["matched"] for r in results):
            seen_src, total = set(), 0
            for r in results:
                for sp, tp, rel, size in r["matched"]:
                    total += size
                    if sp not in seen_src:
                        seen_src.add(sp)
                        total += size
            tr2 = Tracker(total=total)
            cache = {}

            def progress(n):
                self.prog(tr2.add(n))

            for r in results:
                for j, (sp, tp, rel, size) in enumerate(r["matched"], 1):
                    if cancel.is_set():
                        raise Cancelled()
                    tr2.label = f"Verifying {r['letter']}: {j:,}/{len(r['matched']):,}"
                    try:
                        if sp not in cache:
                            cache[sp] = hash_file(sp, cancel, progress)
                        if hash_file(tp, cancel, progress) != cache[sp]:
                            r["diff"].append((rel, size))
                    except Cancelled:
                        raise
                    except Exception as e:
                        errors.append(as_error(e, "E110", sp))
            tr = tr2

        out("", display=False)
        for r in results:
            n = len(r["missing"])
            out("=" * 64, "hd")
            out(f"{r['letter']}: {r['path']}   |   {r['count']:,} files", "hd")
            out(f"Missing files: {n:,}" + (f"   ({fmt_size(sum(s for _, s in r['missing']))})" if n else ""),
                "err" if n else "ok")
            if deep:
                d = len(r["diff"])
                out(f"Different content: {d:,}", "err" if d else "ok")
            if not n and not (deep and r["diff"]):
                out("Nothing missing - this target has everything from the source.", "ok")
            for j, (rel, size) in enumerate(r["missing"]):
                out(f"   {rel}   ({fmt_size(size)})", display=j < DISPLAY_LIMIT)
            if n > DISPLAY_LIMIT:
                self.say(f"   ... {n - DISPLAY_LIMIT:,} more (use Save report for the full list)", "dim")
            if deep and r["diff"]:
                out("   Files with different content:", "warn")
                for rel, size in r["diff"][:DISPLAY_LIMIT]:
                    out(f"   ~ {rel}   ({fmt_size(size)})")
        self.report = "\n".join(report)
        self.prog(tr.finish())
        self.say("", "")
        self.say(f"Compare finished in {fmt_time(time.monotonic() - t0)}.", "ok")
        if errors:
            for e in errors[:25]:
                self.say(f"X {e}", "err")
            self.say(f"Errors: {len(errors)}   ({summarize_errors(errors)})", "err")


class Launcher(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("moverman")
        self.resizable(False, False)
        setup_style(self)
        f = ttk.Frame(self, padding=30)
        f.pack()
        ttk.Label(f, text="moverman", style="Title.TLabel").pack()
        ttk.Label(f, text="Safe copy, move and compare for files, folders and drives",
                  style="Sub.TLabel").pack(pady=(2, 20))
        row = ttk.Frame(f)
        row.pack()
        for col, (name, desc, cls) in enumerate((
                ("Move", "Copy or move files onto a drive", MoveWindow),
                ("Compare", "Find files missing from other drives", CompareWindow))):
            cell = ttk.Frame(row)
            cell.grid(row=0, column=col, padx=12)
            ttk.Button(cell, text=name, style="Mode.TButton", width=12,
                       command=lambda c=cls: self.open_mode(c)).pack()
            ttk.Label(cell, text=desc, style="Sub.TLabel", wraplength=160, justify="center").pack(pady=(6, 0))
        foot = ttk.Frame(f)
        foot.pack(fill="x", pady=(24, 0))
        ttk.Label(foot, text=f"v{__version__}", style="Sub.TLabel").pack(side="left")
        ttk.Button(foot, text="Error codes", command=lambda: show_error_codes(self)).pack(side="right")

    def open_mode(self, cls):
        self.withdraw()
        cls(self)


def main():
    enable_dpi()
    Launcher().mainloop()


if __name__ == "__main__":
    main()

