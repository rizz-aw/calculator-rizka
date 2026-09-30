import ast
import math
import operator
import random
import re
import tkinter as tk
import tkinter.font as tkfont

class CalcError(Exception):
    pass


ANGLE = {"DEG": math.pi / 180, "RAD": 1.0, "GRAD": math.pi / 200}

# token tampilan -> nama internal
DISPLAY = {
    "sin⁻¹(": "asin(", "cos⁻¹(": "acos(", "tan⁻¹(": "atan(",
    "sinh⁻¹(": "asinh(", "cosh⁻¹(": "acosh(", "tanh⁻¹(": "atanh(",
    "sinh(": "sinh(", "cosh(": "cosh(", "tanh(": "tanh(",
    "sin(": "sin(", "cos(": "cos(", "tan(": "tan(",
    "log₂(": "log2(", "log(": "log(", "ln(": "ln(",
    "√(": "sqrt(", "∛(": "cbrt(", "abs(": "abs(",
    "nPr(": "perm(", "nCr(": "comb(",
    "π": "pi", "φ": "phi", "Rand": "rand",
}
_NAME_RE = re.compile("|".join(map(re.escape, sorted(DISPLAY, key=len, reverse=True))))
_FUNC_TOKENS = [t for t in DISPLAY if t not in ("π", "φ")]
_IMPL_RE = re.compile(r"(?<=[\d\)πφe!%])(?=[(πφe]|"
                      + "|".join(map(re.escape, sorted(_FUNC_TOKENS, key=len, reverse=True))) + ")")


def _need(ok, msg):
    if not ok:
        raise CalcError(msg)


def _int(x, name):
    _need(abs(x - round(x)) < 1e-9 and x >= 0, f"{name} hanya untuk bilangan bulat ≥ 0")
    return int(round(x))


def _make_funcs(mode):
    k = ANGLE[mode]

    def tan(x):
        _need(abs(math.cos(x * k)) > 1e-12, "tan tidak terdefinisi di sudut ini")
        return math.tan(x * k)

    def fact(n):
        n = _int(n, "Faktorial")
        _need(n <= 170, "Angkanya kebesaran untuk faktorial!")
        return float(math.factorial(n))

    def perm(n, r):
        n, r = _int(n, "nPr"), _int(r, "nPr")
        _need(r <= n, "nPr: r tidak boleh lebih besar dari n")
        return float(math.perm(n, r))

    def comb(n, r):
        n, r = _int(n, "nCr"), _int(r, "nCr")
        _need(r <= n, "nCr: r tidak boleh lebih besar dari n")
        return float(math.comb(n, r))

    def cbrt(x):
        return math.copysign(abs(x) ** (1 / 3), x)

    def pos(f, name):
        return lambda x: (_need(x > 0, f"{name} hanya untuk bilangan positif"), f(x))[1]

    return {
        "sin": (lambda x: math.sin(x * k), 1), "cos": (lambda x: math.cos(x * k), 1),
        "tan": (tan, 1),
        "asin": (lambda x: (_need(-1 <= x <= 1, "sin⁻¹: nilai harus di antara −1 dan 1"), math.asin(x) / k)[1], 1),
        "acos": (lambda x: (_need(-1 <= x <= 1, "cos⁻¹: nilai harus di antara −1 dan 1"), math.acos(x) / k)[1], 1),
        "atan": (lambda x: math.atan(x) / k, 1),
        "sinh": (math.sinh, 1), "cosh": (math.cosh, 1), "tanh": (math.tanh, 1),
        "asinh": (math.asinh, 1),
        "acosh": (lambda x: (_need(x >= 1, "cosh⁻¹: nilai harus ≥ 1"), math.acosh(x))[1], 1),
        "atanh": (lambda x: (_need(-1 < x < 1, "tanh⁻¹: nilai harus di antara −1 dan 1"), math.atanh(x))[1], 1),
        "log": (pos(math.log10, "log"), 1), "log2": (pos(math.log2, "log₂"), 1),
        "ln": (pos(math.log, "ln"), 1),
        "sqrt": (lambda x: (_need(x >= 0, "Akar bilangan negatif tidak bisa"), math.sqrt(x))[1], 1),
        "cbrt": (cbrt, 1), "abs": (abs, 1), "fact": (fact, 1),
        "perm": (perm, 2), "comb": (comb, 2),
    }


_BINOPS = {ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul,
           ast.Div: operator.truediv, ast.Pow: operator.pow, ast.Mod: operator.mod}
_PHI = (1 + math.sqrt(5)) / 2


def _ev(node, funcs):
    if isinstance(node, ast.Expression):
        return _ev(node.body, funcs)
    if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)):
        return float(node.value)
    if isinstance(node, ast.Name):
        if node.id == "pi": return math.pi
        if node.id == "e": return math.e
        if node.id == "phi": return _PHI
        if node.id == "rand": return random.random()
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
        v = _ev(node.operand, funcs)
        return -v if isinstance(node.op, ast.USub) else v
    if isinstance(node, ast.BinOp) and type(node.op) in _BINOPS:
        a, b = _ev(node.left, funcs), _ev(node.right, funcs)
        if isinstance(node.op, ast.Pow):
            _need(abs(b) <= 1000, "Pangkatnya kebesaran!")
            _need(not (a < 0 and abs(b - round(b)) > 1e-9), "Pangkat pecahan dari bilangan negatif")
        return _BINOPS[type(node.op)](a, b)
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in funcs and not node.keywords):
        fn, n = funcs[node.func.id]
        _need(len(node.args) == n, "Jumlah argumen fungsi tidak sesuai")
        return fn(*[_ev(a, funcs) for a in node.args])
    raise CalcError("Ekspresi tidak valid")


def _expand_fact(s):
    while "!" in s:
        i = s.index("!")
        _need(i > 0, "Faktorial butuh angka di depannya")
        if s[i - 1] == ")":
            depth, k = 0, i - 1
            while k >= 0:
                depth += s[k] == ")"
                depth -= s[k] == "("
                if depth == 0:
                    break
                k -= 1
            _need(k >= 0, "Kurung tidak seimbang")
            start = k
        else:
            m = re.search(r"(\d+(?:\.\d+)?|π|φ|e)$", s[:i])
            _need(m is not None, "Faktorial butuh angka di depannya")
            start = m.start()
        s = s[:start] + "fact(" + s[start:i] + ")" + s[i + 1:]
    return s


def format_number(v):
    if abs(v) < 1e-12:
        v = 0.0
    if v == int(v) and abs(v) < 1e15:
        s = str(int(v))
    else:
        s = f"{v:.10g}"
        if "e" in s:
            m, ex = s.split("e")
            s = f"{m}×10^({int(ex)})"
    return s.replace("-", "−")


def evaluate_value(expr, mode="DEG"):
    _need(expr.strip() != "", "Ketik sesuatu dulu, partner!")
    s = expr + ")" * (expr.count("(") - expr.count(")"))
    s = _IMPL_RE.sub("*", s)
    s = re.sub(r"(?<=[\)πφe])(?=\d)", "*", s)
    s = _expand_fact(s)
    s = _NAME_RE.sub(lambda m: DISPLAY[m.group()], s)
    s = (s.replace("%", "/100").replace("mod", "%").replace("×", "*").replace("÷", "/")
          .replace("−", "-").replace("^", "**"))
    try:
        val = _ev(ast.parse(s, mode="eval"), _make_funcs(mode))
    except CalcError:
        raise
    except ZeroDivisionError:
        raise CalcError("Tidak bisa dibagi nol!")
    except OverflowError:
        raise CalcError("Hasilnya kebesaran!")
    except (SyntaxError, ValueError, TypeError, RecursionError):
        raise CalcError("Format ekspresi belum benar")
    _need(not (math.isnan(val) or math.isinf(val)), "Hasil tidak terdefinisi")
    return val


def calculate(expr, mode="DEG"):
    return format_number(evaluate_value(expr, mode))


# ==========================================================================
#  TAMPILAN
# ==========================================================================
FONT = "Comic Sans MS"
WOOD = ["#C58B4E", "#B87D42", "#CF9558", "#BE8347"]
DARK, INK, CREAM = "#5B3213", "#4A2A10", "#FFF3D6"
KIND_COLORS = {
    "num": ("#E8B37A", INK), "op": ("#F6C445", INK), "fn": ("#8B5A2B", CREAM),
    "mem": ("#6F8F72", "#FFFFFF"), "clr": ("#F28B82", INK), "eq": ("#D64541", "#FFFFFF"),
    "shift": ("#E58E3A", INK),
}
GREETING = "Yeehaw, partner! Ayo berhitung!"


def shade(hex_color, f):
    h = hex_color.lstrip("#")
    r, g, b = (int(h[i:i + 2], 16) for i in (0, 2, 4))
    if f >= 0:
        r, g, b = (int(c + (255 - c) * f) for c in (r, g, b))
    else:
        r, g, b = (int(c * (1 + f)) for c in (r, g, b))
    return f"#{r:02X}{g:02X}{b:02X}"


def rrect(c, x1, y1, x2, y2, r, **kw):
    r = min(r, (x2 - x1) / 2, (y2 - y1) / 2)
    pts = [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2,
           x2 - r, y2, x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]
    return c.create_polygon(pts, smooth=True, **kw)


class WoodButton:
    def __init__(self, c, x, y, w, h, label, kind, action, fsize):
        self.c, self.action, self.fsize = c, action, fsize
        self.base, self.txt = KIND_COLORS[kind]
        self.tag = f"btn{id(self)}"
        r = min(w, h) * 0.28
        rrect(c, x, y + 3, x + w, y + h + 3, r, fill=shade(self.base, -0.45), outline="")
        self.body = rrect(c, x, y, x + w, y + h, r, fill=self.base, outline=DARK,
                          width=2, tags=self.tag)
        c.create_line(x + r, y + h * 0.15, x + w - r, y + h * 0.15, fill=shade(self.base, 0.4),
                      width=3, capstyle="round", tags=self.tag)
        self.text = c.create_text(x + w / 2, y + h / 2 + 1, text="", fill=self.txt,
                                  tags=self.tag)
        self.set_label(label)
        self.pressed = False
        for ev, fn in (("<Enter>", self._enter), ("<Leave>", self._leave),
                       ("<ButtonPress-1>", self._down), ("<ButtonRelease-1>", self._up)):
            c.tag_bind(self.tag, ev, fn)

    def set_label(self, text):
        n = len(text)
        size = self.fsize if n <= 3 else int(self.fsize * (0.82 if n <= 5 else 0.68))
        self.c.itemconfig(self.text, text=text, font=(FONT, max(7, size), "bold"))

    def highlight(self, on):
        self.base = shade(KIND_COLORS["shift"][0], 0.3) if on else KIND_COLORS["shift"][0]
        self.c.itemconfig(self.body, fill=self.base)

    def _enter(self, _):
        self.c.itemconfig(self.body, fill=shade(self.base, 0.18))
        self.c.config(cursor="hand2")

    def _unpress(self):
        if self.pressed:
            self.c.move(self.tag, 0, -3)
            self.pressed = False

    def _leave(self, _):
        self.c.itemconfig(self.body, fill=self.base)
        self.c.config(cursor="")
        self._unpress()

    def _down(self, _):
        if not self.pressed:
            self.c.move(self.tag, 0, 3)
            self.pressed = True

    def _up(self, _):
        if self.pressed:
            self._unpress()
            self.action()


def I(t): return ("ins", t)
def C(n): return ("cmd", n)
def B(label, kind, prim, slabel=None, sec=None, span=1): return (label, kind, prim, slabel, sec, span)


ROWS = [
    [B("2nd", "shift", C("shift")), B("DEG", "fn", C("mode")), B("MC", "mem", C("mc")),
     B("MR", "mem", C("mr")), B("M+", "mem", C("m+")), B("M−", "mem", C("m-"))],
    [B("sin", "fn", I("sin("), "sin⁻¹", I("sin⁻¹(")), B("cos", "fn", I("cos("), "cos⁻¹", I("cos⁻¹(")),
     B("tan", "fn", I("tan("), "tan⁻¹", I("tan⁻¹(")), B("sinh", "fn", I("sinh("), "sinh⁻¹", I("sinh⁻¹(")),
     B("cosh", "fn", I("cosh("), "cosh⁻¹", I("cosh⁻¹(")), B("tanh", "fn", I("tanh("), "tanh⁻¹", I("tanh⁻¹("))],
    [B("log", "fn", I("log("), "10ˣ", I("10^(")), B("ln", "fn", I("ln("), "eˣ", I("e^(")),
     B("√", "fn", I("√("), "∛", I("∛(")), B("x²", "fn", I("^2"), "x³", I("^3")),
     B("xʸ", "fn", I("^"), "2ˣ", I("2^(")), B("1/x", "fn", I("1/("), "|x|", I("abs("))],
    [B("π", "fn", I("π"), "φ", I("φ")), B("e", "fn", I("e"), "Rand", I("Rand")),
     B("(", "fn", I("(")), B(")", "fn", I(")")),
     B("n!", "fn", I("!"), "nCr", I("nCr(")), B("mod", "fn", I("mod"), "nPr", I("nPr("))],
    [B("7", "num", I("7")), B("8", "num", I("8")), B("9", "num", I("9")),
     B("÷", "op", I("÷")), B("⌫", "clr", C("back")), B("C", "clr", C("clear"))],
    [B("4", "num", I("4")), B("5", "num", I("5")), B("6", "num", I("6")),
     B("×", "op", I("×")), B("EXP", "fn", I("×10^(")), B("Ans", "fn", C("ans"))],
    [B("1", "num", I("1")), B("2", "num", I("2")), B("3", "num", I("3")),
     B("−", "op", I("−")), B("±", "fn", C("neg")), B("%", "fn", I("%"))],
    [B("0", "num", I("0")), B(".", "num", I(".")), B(",", "fn", I(",")),
     B("+", "op", I("+")), B("=", "eq", C("eval"), span=2)],
]

CONT = ("+", "−", "×", "÷", "^", "^2", "^3", "!", "%", "mod", "×10^(", ",")
BINARY = ("+", "×", "÷", "^")
NO_START = ("×", "÷", "^", "mod", "!", "%", ",", "^2", "^3", "×10^(")
REMOVABLE = sorted(list(DISPLAY) + ["10^(", "e^(", "2^(", "1/(", "×10^(", "mod", "^2", "^3"],
                   key=len, reverse=True)


class Calculator:
    def __init__(self, root):
        self.root = root
        root.title("Kalkulator Desktop — Sains Sheriff Kayu")
        root.geometry("520x860")
        root.minsize(420, 660)
        self.c = tk.Canvas(root, highlightthickness=0, bg="#B87D42")
        self.c.pack(fill="both", expand=True)

        self.expr, self.mode = "", "DEG"
        self.just_done, self.shift, self.hist_open = False, False, False
        self.last_ans, self.mem = "0", 0.0
        self.history = []
        self.hist_text, self.hist_err = "", False
        self.bubble_text, self._bubble_job = GREETING, None
        self.eyes, self.lids, self.shiftables = [], [], []
        self._size, self._job = (0, 0), None

        self.c.bind("<Configure>", self._on_resize)
        root.bind("<Key>", self._key)
        root.update_idletasks()
        self.rebuild()
        root.after(random_ms(), self._blink)

    # ------------------------------------------------------------ resize
    def _on_resize(self, ev):
        if (ev.width, ev.height) == self._size:
            return
        self._size = (ev.width, ev.height)
        if self._job:
            self.root.after_cancel(self._job)
        self._job = self.root.after(50, self.rebuild)

    def rebuild(self):
        c = self.c
        w, h = c.winfo_width(), c.winfo_height()
        if w < 100 or h < 100:
            return
        c.delete("all")
        c.config(cursor="")
        self.W, self.H = w, h
        self.m = max(8, int(w * 0.03))
        self.shiftables = []
        hh = int(max(105, min(h * 0.17, 175)))
        dh = int(max(100, min(h * 0.17, 170)))
        self.hdr_h = hh
        self._wood(w, h)
        self._header(w, hh)
        top = hh + 8
        self._display(w, top, dh)
        self._buttons(w, h, top + dh + 14)
        if self.hist_open:
            self._draw_history()
        self.refresh()

    # ------------------------------------------------------------- dekor
    def _wood(self, w, h):
        c, rnd, ph = self.c, random.Random(7), 64
        for i in range(h // ph + 2):
            y, col = i * ph, WOOD[i % 4]
            c.create_rectangle(-2, y, w + 2, y + ph, fill=col, outline="#7A4A22")
            for _ in range(4):
                gy, pts, x = y + rnd.randint(8, ph - 8), [], 0
                while x <= w + 60:
                    pts += [x, gy + rnd.randint(-2, 2)]
                    x += 60
                c.create_line(pts, smooth=True, fill=shade(col, -0.18))
            if rnd.random() < 0.5:
                kx, ky = rnd.randint(40, max(41, w - 40)), y + ph // 2
                c.create_oval(kx - 9, ky - 5, kx + 9, ky + 5, fill=shade(col, -0.25), outline=shade(col, -0.4))
                c.create_oval(kx - 4, ky - 2, kx + 4, ky + 2, fill=shade(col, -0.4), outline="")
            for nx in (9, w - 9):
                c.create_oval(nx - 3, y + ph // 2 - 3, nx + 3, y + ph // 2 + 3, fill="#6B6B6B", outline="#3E3E3E")

    def _mascot(self, s, ox):
        c, m = self.c, "mascot"
        c.create_polygon(45, 112, 105, 112, 75, 142, fill="#D64541", outline=DARK, width=2, tags=m)
        for dx, dy in ((62, 118), (76, 128), (88, 118)):
            c.create_oval(dx - 2, dy - 2, dx + 2, dy + 2, fill="white", outline="", tags=m)
        c.create_oval(40, 55, 110, 122, fill="#FFD9B3", outline="#7A4A22", width=2, tags=m)
        c.create_oval(14, 42, 136, 74, fill="#A9672B", outline=DARK, width=2, tags=m)
        rrect(c, 42, 8, 108, 60, 18, fill="#B87333", outline=DARK, width=2, tags=m)
        c.create_polygon(43, 48, 107, 48, 108, 38, 42, 38, fill="#C0392B", outline=DARK, tags=m)
        star = []
        for i in range(10):
            a, r = math.radians(-90 + i * 36), (8 if i % 2 == 0 else 3.6)
            star += [75 + r * math.cos(a), 43 + r * math.sin(a)]
        c.create_polygon(star, fill="#FFD34D", outline=DARK, tags=m)
        self.eyes, self.lids = [], []
        for ex in (63, 87):
            self.eyes.append(c.create_oval(ex - 5, 82, ex + 5, 98, fill="#2B1B10", outline="", tags=m))
            c.create_oval(ex - 3, 85, ex, 89, fill="white", outline="", tags=m)
            self.lids.append(c.create_arc(ex - 6, 86, ex + 6, 98, start=200, extent=140, style="arc",
                                          outline="#2B1B10", width=2, state="hidden", tags=m))
        for bx in (55, 95):
            c.create_oval(bx - 8, 98, bx + 8, 107, fill="#FF9AA2", outline="", tags=m)
        c.create_oval(72, 94, 78, 99, fill="#E8A87C", outline="", tags=m)
        c.create_arc(64, 95, 86, 113, start=200, extent=140, style="arc", outline="#7A2E1D", width=2, tags=m)
        c.scale(m, 0, 0, s, s)
        c.move(m, ox, 0)

    def _header(self, w, hh):
        c, s = self.c, hh / 140.0
        ox = max(2, w * 0.01)
        self._mascot(s, ox)
        sx1, sx2 = ox + 140 * s, w - self.m
        sy1, sy2 = hh * 0.12, hh * 0.63
        for rx in (sx1 + 25, sx2 - 25):
            c.create_line(rx, 0, rx, sy1, fill="#E9D8A6", width=3)
        rrect(c, sx1 + 4, sy1 + 6, sx2 + 4, sy2 + 6, 12, fill=shade("#7A4A22", -0.3), outline="")
        rrect(c, sx1, sy1, sx2, sy2, 12, fill="#D9A15F", outline=DARK, width=3)
        for nx, ny in ((sx1 + 12, sy1 + 12), (sx2 - 12, sy1 + 12), (sx1 + 12, sy2 - 12), (sx2 - 12, sy2 - 12)):
            c.create_oval(nx - 3, ny - 3, nx + 3, ny + 3, fill="#777", outline="#333")
        fs = max(9, int((sx2 - sx1) / 14.5))
        mid = (sx1 + sx2) / 2
        c.create_text(mid, sy1 + (sy2 - sy1) * 0.42, text="Kalkulator Desktop", fill=INK, font=(FONT, fs, "bold"))
        c.create_text(mid, sy1 + (sy2 - sy1) * 0.78, text="★ Sains Lengkap  •  Sheriff Kayu ★",
                      fill="#7A3E12", font=(FONT, max(7, int(fs * 0.5)), "bold"))
        by1, by2 = hh * 0.71, hh * 0.96
        rrect(c, sx1 + 12, by1, sx2, by2, 12, fill=CREAM, outline=DARK, width=2)
        c.create_polygon(sx1 + 12, (by1 + by2) / 2 - 5, sx1, (by1 + by2) / 2, sx1 + 12, (by1 + by2) / 2 + 5,
                         fill=CREAM, outline=DARK, width=2)
        c.create_line(sx1 + 12, (by1 + by2) / 2 - 3, sx1 + 12, (by1 + by2) / 2 + 3, fill=CREAM, width=3)
        self.bubble = c.create_text((sx1 + 12 + sx2) / 2, (by1 + by2) / 2, text=self.bubble_text, fill=INK,
                                    font=(FONT, max(8, int(fs * 0.55)), "bold"), width=sx2 - sx1 - 30)

    def _display(self, w, y1, dh):
        c, m = self.c, self.m
        x1, x2, y2 = m, w - m, y1 + dh
        rrect(c, x1 - 6, y1 - 6, x2 + 6, y2 + 6, 18, fill=DARK, outline="")
        rrect(c, x1, y1, x2, y2, 14, fill=CREAM, outline="#3B200C", width=2)
        c.create_line(x1 + 12, y1 + 5, x2 - 12, y1 + 5, fill="white", width=2)
        self.dh, self.davail = dh, (x2 - x1) - 28
        self.status = c.create_text(x1 + 12, y1 + dh * 0.14, anchor="w", fill="#C0392B",
                                    font=(FONT, max(8, int(dh * 0.1)), "bold"))
        self.hist_item = c.create_text(x2 - 12, y1 + dh * 0.40, anchor="e", fill="#8B6B4A",
                                       font=(FONT, max(8, int(dh * 0.11))))
        self.main = c.create_text(x2 - 12, y1 + dh * 0.74, anchor="e", fill=INK,
                                  font=(FONT, int(dh * 0.34), "bold"))
        bw, bh = max(64, dh * 0.62), dh * 0.22
        WoodButton(c, x2 - 12 - bw, y1 + 8, bw, bh, "Riwayat", "mem", self._open_history,
                   max(7, int(bh * 0.45)))

    def _buttons(self, w, h, top):
        m = self.m
        g = max(4, int(min(w, h) * 0.011))
        bw = (w - 2 * m - 5 * g) / 6
        bh = (h - top - m - 7 * g - 3) / 8
        fs = max(8, int(min(bh * 0.36, bw * 0.30)))

        def make(prim, sec):
            def act():
                use = sec if (self.shift and sec) else prim
                if self.shift and sec:
                    self.shift = False
                    self._sync_shift()
                self.do(use)
            return act

        for r, row in enumerate(ROWS):
            col = 0
            for label, kind, prim, sl, sec, span in row:
                x, y = m + col * (bw + g), top + r * (bh + g)
                ww = bw * span + g * (span - 1)
                if label == "DEG":
                    label = self.mode
                btn = WoodButton(self.c, x, y, ww, bh, label, kind, make(prim, sec), fs)
                if sl:
                    self.shiftables.append((btn, label, sl))
                    if self.shift:
                        btn.set_label(sl)
                if kind == "shift":
                    self.shift_btn = btn
                    btn.highlight(self.shift)
                if prim == C("mode"):
                    self.mode_btn = btn
                col += span

    def _sync_shift(self):
        for btn, prim, sec in self.shiftables:
            btn.set_label(sec if self.shift else prim)
        self.shift_btn.highlight(self.shift)
        self.refresh()

    # ------------------------------------------------------- riwayat
    def _open_history(self):
        self.hist_open = True
        self.rebuild()

    def _close_history(self):
        self.hist_open = False
        self.rebuild()

    def _draw_history(self):
        c, m = self.c, self.m
        x1, x2, y1, y2 = m, self.W - m, self.hdr_h + 8, self.H - m
        rrect(c, x1, y1, x2, y2, 16, fill=CREAM, outline=DARK, width=3)
        fs = max(9, int(self.W * 0.028))
        c.create_text((x1 + x2) / 2, y1 + fs * 1.6, text="Riwayat Hitungan", fill=INK, font=(FONT, fs + 3, "bold"))
        y, lh = y1 + fs * 3.4, fs * 3.6
        if not self.history:
            c.create_text((x1 + x2) / 2, y + fs * 2, text="Belum ada hitungan, partner!", fill="#8B6B4A", font=(FONT, fs))
        for i, (ex, res) in enumerate(reversed(self.history)):
            if y + lh > y2 - fs * 4.5:
                break
            tag = f"h{i}"
            c.create_rectangle(x1 + 10, y - 2, x2 - 10, y + lh - 6, fill="#F7E3B5", outline="", tags=tag)
            c.create_text(x2 - 20, y + 3, anchor="ne", text=ex, fill="#8B6B4A", font=(FONT, max(8, fs - 3)), tags=tag)
            c.create_text(x2 - 20, y + lh - 10, anchor="se", text="= " + res, fill=INK, font=(FONT, fs, "bold"), tags=tag)
            c.tag_bind(tag, "<Button-1>", lambda e, r=res: self._use_history(r))
            c.tag_bind(tag, "<Enter>", lambda e: c.config(cursor="hand2"))
            c.tag_bind(tag, "<Leave>", lambda e: c.config(cursor=""))
            y += lh
        bw, bh = (x2 - x1 - 30) / 2, fs * 2.6
        WoodButton(c, x1 + 10, y2 - bh - 10, bw, bh, "Hapus", "clr", self._clear_history, fs)
        WoodButton(c, x1 + 20 + bw, y2 - bh - 10, bw, bh, "Tutup", "eq", self._close_history, fs)

    def _use_history(self, res):
        self.hist_open = False
        self.expr, self.just_done = res, True
        self.rebuild()

    def _clear_history(self):
        self.history.clear()
        self.rebuild()

    # ------------------------------------------------------------ logika
    def do(self, action):
        typ, val = action
        (self.press if typ == "ins" else self.command)(val)

    def _clear_err(self):
        if self.hist_err:
            self.hist_err, self.hist_text = False, ""

    def press(self, tok):
        if self.hist_open:
            return
        self._clear_err()
        e = self.expr
        if self.just_done:
            if tok in CONT:
                pass
            elif tok.endswith("(") and tok != "(":
                self.expr, self.just_done = tok + self.last_ans + ")", False
                self.refresh()
                return
            else:
                e = ""
            self.just_done = False
        if tok in NO_START and not e:
            return
        if tok == ".":
            mt = re.search(r"[\d.]+$", e)
            if mt and "." in mt.group():
                return
            if not mt:
                tok = "0."
        elif tok in BINARY and e and e[-1] in "+−×÷^":
            e = e[:-1]
        elif tok == "−" and e and e[-1] in "+−":
            e = e[:-1]
        self.expr = e + tok
        self.refresh()

    def command(self, name):
        if self.hist_open:
            return
        if name != "eval":
            self._clear_err()
        if name == "clear":
            self.expr, self.just_done, self.hist_text = "", False, ""
            self.say("Bersih kinclong!")
        elif name == "back":
            if self.just_done:
                self.expr, self.just_done = "", False
            else:
                for t in REMOVABLE:
                    if self.expr.endswith(t):
                        self.expr = self.expr[:-len(t)]
                        break
                else:
                    self.expr = self.expr[:-1]
        elif name == "mode":
            order = ["DEG", "RAD", "GRAD"]
            self.mode = order[(order.index(self.mode) + 1) % 3]
            self.mode_btn.set_label(self.mode)
            self.say({"DEG": "Mode sudut: derajat", "RAD": "Mode sudut: radian",
                      "GRAD": "Mode sudut: grad"}[self.mode])
        elif name == "shift":
            self.shift = not self.shift
            self._sync_shift()
            self.say("Fungsi 2nd aktif!" if self.shift else GREETING)
            return
        elif name == "ans":
            self.press(self.last_ans)
            return
        elif name == "neg":
            self._negate()
        elif name == "eval":
            self.evaluate()
            return
        elif name in ("m+", "m-"):
            try:
                v = evaluate_value(self.expr or "0", self.mode)
            except CalcError as err:
                self.error(str(err))
                return
            self.mem += v if name == "m+" else -v
            self.say("Disimpan ke memori!")
        elif name == "mr":
            if self.mem == 0:
                self.say("Memori masih kosong.")
            else:
                self.press(format_number(self.mem))
                return
        elif name == "mc":
            self.mem = 0.0
            self.say("Memori dikosongkan.")
        self.refresh()

    def _negate(self):
        e = self.expr
        m1 = re.search(r"\(−(\d+(?:\.\d+)?)\)$", e)
        m2 = re.search(r"\d+(?:\.\d+)?$", e)
        if m1:
            self.expr = e[:m1.start()] + m1.group(1)
        elif m2:
            self.expr = e[:m2.start()] + "(−" + m2.group() + ")"
        elif not e:
            self.expr = "(−"
        self.just_done = False

    def evaluate(self):
        try:
            res = calculate(self.expr, self.mode)
        except CalcError as err:
            self.error(str(err))
            return
        self.history.append((self.expr, res))
        del self.history[:-30]
        self.hist_text, self.hist_err = self.expr + " =", False
        self.expr, self.last_ans, self.just_done = res, res, True
        self.say(random.choice(["Yeehaw! Beres, partner!", "Mantap jiwa, Sheriff!",
                                "Hitungan kelar! ★", "Tepat sasaran!"]))
        self.bounce()
        self.refresh()

    def error(self, msg):
        self.hist_text, self.hist_err = msg, True
        self.say("Waduh, ada yang keliru!")
        self.bounce()
        self.refresh()

    def _fit(self, text, size, bold, avail):
        f = tkfont.Font(family=FONT, size=size, weight="bold" if bold else "normal")
        while f.measure(text) > avail and size > 9:
            size -= 1
            f.configure(size=size)
        while f.measure(text) > avail and len(text) > 4:
            text = "…" + text[2:]
        return text, size

    def refresh(self):
        if not hasattr(self, "main"):
            return
        c = self.c
        txt, sz = self._fit(self.expr or "0", int(self.dh * 0.34), True, self.davail)
        c.itemconfig(self.main, text=txt, font=(FONT, sz, "bold"))
        ht, hs = self._fit(self.hist_text, max(8, int(self.dh * 0.11)), False, self.davail - 90)
        c.itemconfig(self.hist_item, text=ht, font=(FONT, hs),
                     fill="#C0392B" if self.hist_err else "#8B6B4A")
        st = self.mode + ("   M" if self.mem else "") + ("   2nd" if self.shift else "")
        c.itemconfig(self.status, text=st)

    # ---------------------------------------------------------- keyboard
    def _key(self, ev):
        ch, ks = ev.char, ev.keysym
        if self.hist_open:
            if ks == "Escape" or ch == "h":
                self._close_history()
            return
        keymap = {"*": "×", "/": "÷", "-": "−", "+": "+", "^": "^", "(": "(", ")": ")", ".": ".",
                  ",": ",", "%": "%", "!": "!", "p": "π", "e": "e", "m": "mod", "r": "√(",
                  "l": "log(", "n": "ln(", "s": "sin(", "c": "cos(", "t": "tan("}
        if ks in ("Return", "KP_Enter") or ch == "=":
            self.evaluate()
        elif ks == "BackSpace":
            self.command("back")
        elif ks in ("Escape", "Delete"):
            self.command("clear")
        elif ch == "h":
            self._open_history()
        elif ch and ch.isdigit():
            self.press(ch)
        elif ch in keymap:
            self.press(keymap[ch])

    # --------------------------------------------------------- animasi
    def say(self, text, ms=2600):
        self.bubble_text = text
        self._set_bubble()
        if self._bubble_job:
            self.root.after_cancel(self._bubble_job)
        self._bubble_job = self.root.after(ms, self._reset_bubble)

    def _set_bubble(self):
        try:
            self.c.itemconfig(self.bubble, text=self.bubble_text)
        except (tk.TclError, AttributeError):
            pass

    def _reset_bubble(self):
        self.bubble_text = GREETING
        self._set_bubble()

    def bounce(self, step=0):
        seq = [-7, -4, 4, 7]
        if step < len(seq):
            self.c.move("mascot", 0, seq[step])
            self.root.after(70, lambda: self.bounce(step + 1))

    def _blink(self):
        try:
            for e, l in zip(self.eyes, self.lids):
                self.c.itemconfig(e, state="hidden")
                self.c.itemconfig(l, state="normal")
        except tk.TclError:
            pass
        self.root.after(140, self._open_eyes)

    def _open_eyes(self):
        try:
            for e, l in zip(self.eyes, self.lids):
                self.c.itemconfig(e, state="normal")
                self.c.itemconfig(l, state="hidden")
        except tk.TclError:
            pass
        self.root.after(random_ms(), self._blink)


def random_ms():
    return random.randint(2200, 4800)


def main():
    root = tk.Tk()
    Calculator(root)
    root.mainloop()


if __name__ == "__main__":
    main()