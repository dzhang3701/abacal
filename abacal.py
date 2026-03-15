#!/usr/bin/env python3
"""
ABACAL — the number puzzle
Use all given numbers with +, -, *, / (and parentheses) to reach the target.
"""

import os, sys, time, json, math, random, re, ast, signal, argparse, threading, itertools, select, unicodedata
try:    import termios, tty as _tty;  _HAS_TTY = True
except ImportError: _HAS_TTY = False
from pathlib import Path
try: import readline  # activates proper line editing (backspace, arrow keys)
except ImportError: pass

# ── terminal ──────────────────────────────────────────────────────────────────

def term_w():
    try: return min(os.get_terminal_size().columns, 110)
    except: return 80

def term_h():
    try: return os.get_terminal_size().lines
    except: return 24

# Rows the puzzle card needs below the history block (puzzle# + timer + content + prompt).
_PUZZLE_ROWS = 16

def _clip_history(lines):
    """Trim history lines to fit above the puzzle within the current terminal height.
    Clips from the top (oldest entries removed first).  Returns [] if nothing fits."""
    if not lines:
        return []
    available = max(0, term_h() - _PUZZLE_ROWS)
    if available < 3:          # not enough room for even one sep+entry+sep
        return []
    trimmed = lines[-available:]
    # Ensure we start on a separator line for a clean visual edge
    sep_char = '─'
    for i, ln in enumerate(trimmed):
        if sep_char in strip_ansi(ln):
            return trimmed[i:]
    return trimmed

def clear():
    print('\033[2J\033[H', end='', flush=True)

# ── palette ───────────────────────────────────────────────────────────────────

RST  = '\033[0m'
BOLD = '\033[1m'

def fg(n): return f'\033[38;5;{n}m'

P = {
    'cyan':   fg(51),
    'yellow': fg(220),
    'green':  fg(82),
    'red':    fg(196),
    'orange': fg(208),
    'gray':   fg(252),   # bright enough to read easily
    'lgray':  fg(255),
    'white':  fg(255),
    'teal':   fg(43),
    'dgray':  fg(246),   # dim but still readable
    'gold':   fg(178),
}

def c(color, *text, b=False):
    return P.get(color, '') + (BOLD if b else '') + ''.join(str(t) for t in text) + RST

def strip_ansi(s):
    return re.sub(r'\033\[[0-9;]*m', '', s)

def vlen(s):
    s = strip_ansi(s)
    return sum(2 if unicodedata.east_asian_width(ch) in ('W', 'F') else 1 for ch in s)

def center(text, w=None):
    width = w or term_w()
    return ' ' * max(0, (width - vlen(text)) // 2) + text

def hr():
    return center(P['dgray'] + '─' * (term_w() - 8) + RST)

# ── resize handling ───────────────────────────────────────────────────────────
# SIGWINCH sets a flag; the timer thread and prompt_input both check it.

_resize_flag = threading.Event()

def _sigwinch(sig, frame):
    _resize_flag.set()

# ── live timer ────────────────────────────────────────────────────────────────
#
# The puzzle card always leaves row 3 blank (see draw_puzzle layout).
# This thread writes the ticking clock to that fixed row.

class LiveTimer:
    def __init__(self):
        self.t0        = None
        self._stop     = threading.Event()
        self._thread   = None
        self.redraw_fn = None   # set to a callable that redraws the current puzzle
        self.timer_row = 3      # updated by play() based on history height

    def start(self):
        """Start display thread. Preserves t0 if already set (resume after redraw)."""
        if self.t0 is None:
            self.t0 = time.time()
        self._stop.clear()
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()

    def _run(self):
        while not self._stop.wait(0.05):
            # Resize: full redraw then fall through to update timer row
            if _resize_flag.is_set():
                _resize_flag.clear()
                if self.redraw_fn:
                    self.redraw_fn()
            elapsed = time.time() - self.t0
            line    = center(fg(87) + BOLD + f'{elapsed:.2f} s' + RST)
            sys.stdout.write(f'\033[s\033[{self.timer_row};1H\033[K{line}\033[u')
            sys.stdout.flush()

    def stop(self):
        """Stop thread, return elapsed seconds rounded to 2 dp."""
        self._stop.set()
        if self._thread:
            self._thread.join(timeout=0.3)
        return round(time.time() - self.t0, 2) if self.t0 else 0.0

    def reset(self):
        self.stop()
        self.t0 = None

# ── storage ───────────────────────────────────────────────────────────────────

SESSION_DIR = Path.home() / '.abacal' / 'sessions'

def save_session(log, difficulty):
    SESSION_DIR.mkdir(parents=True, exist_ok=True)
    fname = SESSION_DIR / f'{time.strftime("%Y%m%d_%H%M%S")}.json'
    fname.write_text(json.dumps({'difficulty': difficulty, 'log': log}, indent=2))

# ── solver ────────────────────────────────────────────────────────────────────
#
# Partition-based enumeration with memoization, ported from enumeratorCore.js.
#
# Key ideas:
#  • Split the sorted number list into groups; recurse each group with the
#    *opposite* operation (additive ↔ multiplicative).  Memoize on (subset, op).
#  • For each partition, try all 2^k−1 sign/factor masks to combine k groups.
#  • _clean_canonical() reorders commutative terms (sort key from clean() in JS)
#    so that `3+7+4` and `7+4+3` produce the same string → deduplicated.

_TOL = 1e-9

def _opp_type(ch):
    if ch in '+-': return 0
    if ch in '*/': return 1
    return -1

# ── user-expression canonicalizer ─────────────────────────────────────────────
# Converts a user's expression (e.g. "7*3+4") to the same canonical form the
# solver produces (e.g. "3*7+4"), so it can be matched against the solutions list.

def _flatten_add(node, neg=False):
    """Flatten a±b±c into [(sign, node)] with sign propagation through sub-chains."""
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub)):
        left  = _flatten_add(node.left, neg)
        right = _flatten_add(node.right, neg ^ isinstance(node.op, ast.Sub))
        return left + right
    return [('-' if neg else '+', node)]

def _flatten_mul(node, inv=False):
    """Flatten a*/b*/c into [(op, node)] with inversion propagation."""
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Mult, ast.Div)):
        left  = _flatten_mul(node.left, inv)
        right = _flatten_mul(node.right, inv ^ isinstance(node.op, ast.Div))
        return left + right
    return [('/' if inv else '*', node)]

def _canon_node(node, final=False):
    if isinstance(node, ast.Constant):
        v = node.value
        return str(int(v)) if isinstance(v, (int, float)) and abs(v - round(v)) < 1e-9 else str(v)
    if not isinstance(node, ast.BinOp):
        try:    return ast.unparse(node)
        except: return '?'

    if isinstance(node.op, (ast.Add, ast.Sub)):
        parts = _flatten_add(node)
        sp    = [(oc, _canon_node(n, False)) for oc, n in parts]
        def _ak(p):
            is_n = bool(re.match(r'^\d+$', p[1]))
            return (int(is_n), 0 if p[0] == '+' else 1,
                    -int(p[1]) if is_n else -len(p[1]), p[1])
        sp.sort(key=_ak)
        while sp and sp[0][0] == '-':
            sp = sp[1:] + [sp[0]]
        result = ''.join(oc + te for oc, te in sp)[1:]
        return result if final else '(' + result + ')'

    # Mult or Div
    parts = _flatten_mul(node)
    sp    = [(oc, _canon_node(n, False)) for oc, n in parts]
    if sum(1 for p in sp if p[0] == '/') > 1:
        def _sort_mul(ps):
            ps = [('*', p[1]) for p in ps]
            ps.sort(key=lambda p: (1 if p[1].startswith('(') else 0, len(p[1]), p[1]))
            return ''.join(oc + te for oc, te in ps)[1:]
        num = [p for p in sp if p[0] == '*']
        den = [p for p in sp if p[0] == '/']
        return (_sort_mul(num) if num else '1') + '/(' + _sort_mul(den) + ')'
    sp.sort(key=lambda p: (0 if p[0] == '*' else 1,
                           1 if p[1].startswith('(') else 0,
                           len(p[1]), p[1]))
    return ''.join(oc + te for oc, te in sp)[1:]

def _expand_implied_mul(s):
    """Expand implied multiplication: 2(3+4)→2*(3+4), (a)(b)→(a)*(b), (a)2→(a)*2."""
    s = re.sub(r'(\d)\(',  r'\1*(', s)
    s = re.sub(r'\)\(',    r')*(', s)
    s = re.sub(r'\)(\d)',  r')*\1', s)
    return s

def _canonicalize_user_expr(expr_str):
    """Normalize a user's expression string to the same canonical form as the solver."""
    s = re.sub(r'\s+', '', expr_str).replace('×', '*').replace('÷', '/')
    s = _expand_implied_mul(s)
    try:
        tree = ast.parse(s, mode='eval')
        return _canon_node(tree.body, final=True)
    except Exception:
        return s

def _display_sol(s):
    """Convert canonical solution to display form: omit × before '(', use × elsewhere."""
    return s.replace('*(', '(').replace('*', '×')

def _clean_canonical(sol, final=False):
    """Canonicalise an expression so reorderings of commutative ops are identical."""
    if not sol: return sol
    if sol[0] == '(':
        op  = 0
        sol = sol[1:-1]
    else:
        op = 1
    # Split at depth-0 operators of matching type
    depth, prev, parts = 0, 0, []
    for i in range(1, len(sol)):
        c = sol[i]
        if c == '(':   depth += 1
        elif c == ')': depth -= 1
        if depth == 0 and _opp_type(c) == op:
            parts.append((sol[prev], sol[prev+1:i]))
            prev = i
    parts.append((sol[prev], sol[prev+1:]))

    if op == 1:  # multiplicative
        if sum(1 for p in parts if p[0] == '/') > 1:
            num_s  = ''.join('*' + p[1] for p in parts if p[0] == '*') or '*1'
            den_s  = ''.join('*' + p[1] for p in parts if p[0] == '/') or '*1'
            return _clean_canonical(num_s, False) + '/(' + _clean_canonical(den_s, False) + ')'
        parts.sort(key=lambda p: (0 if p[0]=='*' else 1,
                                  1 if p[1].startswith('(') else 0,
                                  len(p[1])))
        return ''.join(oc+te for oc,te in parts)[1:]   # strip leading '*'

    else:  # additive
        def _add_key(p):
            is_n = p[1].isdigit()
            return (int(is_n), 0 if p[0]=='+' else 1,
                    -int(p[1]) if is_n else -len(p[1]))
        parts.sort(key=_add_key)
        if parts[0][0] == '-':
            parts = parts[1:] + [parts[0]]
        result = ''.join(oc+te for oc,te in parts)[1:]  # strip leading '+'
        return result if final else '(' + result + ')'


def _enumerate(numbers):
    """Core: enumerate ALL reachable (value, expr) pairs from numbers.
    Returns a flat list; caller filters for a specific target or groups by value."""
    nums    = tuple(sorted(float(x) for x in numbers))
    n_total = len(nums)
    memo    = {}

    def _fmt(v):
        iv = int(v)
        return str(iv) if abs(v - iv) < _TOL else str(round(v, 9))

    def _enum(nums_t, op):
        key = (nums_t, op)
        if key in memo: return memo[key]
        n, nums_l, ret = len(nums_t), list(nums_t), []

        if n == 1:
            memo[key] = [(nums_l[0], _fmt(nums_l[0]))]
            return memo[key]

        seen_parts = set()

        def generate(idx, prev, cur):
            if idx == n:
                if len(cur) == 1: return
                pk = tuple(sorted(tuple(sorted(s)) for s in cur))
                if pk in seen_parts: return
                seen_parts.add(pk)
                poss = [_enum(tuple(sorted(s)), 1-op) for s in cur]
                for terms in itertools.product(*poss):
                    attain = set()
                    for mask in range((1 << len(cur)) - 1):
                        val, parts, ok = float(op), [], True
                        for i, (tv, te) in enumerate(terms):
                            inc = not bool(mask & (1 << i))
                            if not inc and abs(tv - op) < _TOL: ok=False; break
                            if op == 0:
                                val += tv if inc else -tv
                                oc = '+' if inc else '-'
                            else:
                                if not inc and abs(tv) < _TOL: ok=False; break
                                val = val*tv if inc else val/tv
                                oc = '*' if inc else '/'
                            if math.isnan(val) or math.isinf(val): ok=False; break
                            parts.append((oc, te))
                        if ok and val >= -_TOL:
                            ak = round(val / _TOL)
                            if ak not in attain:
                                attain.add(ak)
                                expr = ''.join(oc+te for oc,te in parts)
                                if op == 0: expr = '(' + expr + ')'
                                ret.append((val, _clean_canonical(expr, n == n_total)))
                return
            v, ns = nums_l[idx], len(cur)
            cur.append([v]);  generate(idx+1, ns, cur);  cur.pop()
            start = prev if (idx > 0 and v == nums_l[idx-1]) else 0
            for i in range(start, ns):
                cur[i].append(v);  generate(idx+1, i, cur);  cur[i].pop()

        generate(0, 0, [])
        if len(set(nums_l)) < n:
            seen_e, deduped = set(), []
            for item in ret:
                k = (round(item[0]/_TOL), item[1])
                if k not in seen_e: seen_e.add(k); deduped.append(item)
            ret = deduped
        memo[key] = ret
        return ret

    all_out = []
    for op in (0, 1):
        all_out.extend(_enum(nums, op))
    return all_out


def solve(numbers, target):
    """Return canonical deduplicated solutions for a specific target."""
    all_out = _enumerate(numbers)
    return list({expr for val, expr in all_out if abs(val - target) < _TOL})


def solve_all(numbers):
    """Enumerate once; return {int_value: [solutions]} for all reachable integers."""
    by_val = {}
    for val, expr in _enumerate(numbers):
        if val > _TOL and abs(val - round(val)) < _TOL:
            k = int(round(val))
            by_val.setdefault(k, set()).add(expr)
    return {k: list(v) for k, v in by_val.items()}

# ── difficulty ────────────────────────────────────────────────────────────────

DIFF_COLORS = {'easy': 'green', 'medium': 'yellow', 'hard': 'orange', 'expert': 'red'}
DIFF_DOTS   = {'easy': '●○○○', 'medium': '●●○○', 'hard': '●●●○', 'expert': '●●●●'}

DIFF_PARAMS = {
    'easy':   {'n': (4, 4), 'nums': (1, 12), 'target': (5,  80),  'min_s': 1, 'max_s': 4},
    'medium': {'n': (4, 5), 'nums': (1, 20), 'target': (10, 300), 'min_s': 1, 'max_s': 4},
    'hard':   {'n': (5, 5), 'nums': (2, 20), 'target': (20, 500), 'min_s': 1, 'max_s': 3},
    'expert': {'n': (6, 6), 'nums': (2, 25), 'target': (50, 999), 'min_s': 1, 'max_s': 2},
}

def calc_difficulty(solutions, nums):
    """
    Assess difficulty from:
      - solution count (scarcity)
      - division usage (division required = harder)
      - expression nesting depth (complex groupings = harder)
      - number count (more numbers = harder search space)
    """
    n, count = len(nums), len(solutions)
    if count == 0: return 'impossible', 99

    scarcity = (10 if count == 1  else 8 if count <= 3  else
                6  if count <= 10 else 4  if count <= 30 else
                2  if count <= 80 else 0)

    div_n = sum(1 for s in solutions if '/' in s)
    div_r = div_n / count
    div   = (4 if div_r > 0.8 else 3 if div_r > 0.5 else 1 if div_r > 0 else 0)

    avg_depth = sum(s.count('(') for s in solutions) / count
    nest      = (3 if avg_depth >= 3 else 2 if avg_depth >= 2 else
                 1 if avg_depth >= 1 else 0)

    size  = (n - 4) * 2   # 0 for n=4, 2 for n=5, 4 for n=6
    total = scarcity + div + nest + size

    label = ('expert' if total >= 16 else 'hard'   if total >= 10 else
             'medium' if total >= 5  else 'easy')
    return label, total

def generate_puzzle(difficulty, tries=200):
    p     = DIFF_PARAMS[difficulty]
    max_s = p.get('max_s', 4)
    min_s = p['min_s']
    tmin, tmax = p['target']

    for _ in range(tries):
        n    = random.randint(*p['n'])
        nums = sorted(random.randint(*p['nums']) for _ in range(n))

        # Enumerate ALL reachable values at once; pick a qualifying target.
        # This is much faster than calling solve() per-target because the
        # memoised partition enumeration is shared across all targets.
        all_vals = solve_all(nums)
        candidates = [
            (t, sols) for t, sols in all_vals.items()
            if tmin <= t <= tmax and min_s <= len(sols) <= max_s
        ]
        if not candidates: continue
        target, sols = random.choice(candidates)
        dlabel, _ = calc_difficulty(sols, nums)
        return nums, target, sols, dlabel

    return [2, 3, 4, 5], 14, ['5+4+3+2'], 'easy'

def build_puzzle_info(sols, n_sols):
    """One-line info string shown when player presses [i]."""
    if not sols:
        return c('dgray', 'no information available')
    n_str = f'{n_sols} solution{"s" if n_sols != 1 else ""}'
    return c('dgray', n_str)


def _top_op_binary(expr):
    """Return the root-level operator only if the expression is strictly binary
    (exactly one depth-0 operator of the dominant type, i.e. exactly two top-level terms).
    Returns None for A+B+C, A+B-C, A*B*C, etc."""
    s = expr.strip()
    depth, add_ops, mul_ops = 0, [], []
    for i, ch in enumerate(s):
        if ch == '(':   depth += 1
        elif ch == ')': depth -= 1
        elif depth == 0:
            if ch in '+-' and i > 0: add_ops.append(ch)
            elif ch in '*/':         mul_ops.append(ch)
    if add_ops:
        return add_ops[-1] if len(add_ops) == 1 else None
    if mul_ops:
        return mul_ops[-1] if len(mul_ops) == 1 else None
    return None


def generate_hint(sols, nums, target):
    """Concise operational hint derived from the solution set."""
    if not sols:
        return c('dgray', 'no hint available')

    OP_NAMES = {'+': 'addition', '-': 'subtraction',
                '*': 'multiplication', '/': 'division'}
    count    = len(sols)

    all_div = all('/' in s for s in sols)
    no_mul  = not any('*' in s for s in sols)

    # Top-level operation: only assert if ALL solutions are strictly binary (A op B)
    # with the same operator — never fires for A+B+C or A+B-C style expressions.
    binary_ops = [_top_op_binary(s) for s in sols]
    best_top_op = None
    if all(op is not None for op in binary_ops):
        unique = set(binary_ops)
        if len(unique) == 1:
            best_top_op = unique.pop()

    avg_d = sum(s.count('(') for s in sols) / count

    # Most-common multiplied pair  e.g. 3*7 appearing in many solutions
    pair_cnts = {}
    for s in sols:
        for a, b in re.findall(r'(\d+)\*(\d+)', s):
            k = tuple(sorted((int(a), int(b))))
            pair_cnts[k] = pair_cnts.get(k, 0) + 1
    best_pair      = max(pair_cnts, key=pair_cnts.__getitem__) if pair_cnts else None
    best_pair_frac = pair_cnts[best_pair] / count if best_pair else 0

    # ── return the most informative hint ──────────────────────────────
    if all_div:
        return c('dgray', 'division is required')

    if no_mul:
        return c('dgray', 'no multiplication needed')

    if best_top_op:
        return c('dgray', f'the final step uses {OP_NAMES[best_top_op]}')

    if best_pair_frac >= 0.55:
        a, b = best_pair
        return c('dgray', f'try {a} × {b} as a starting point')

    if avg_d >= 3:
        return c('dgray', 'deep nesting is required')

    # Fallback: name an unused operation, or note all four are present
    unused = [name for op, name in [('+', 'addition'), ('-', 'subtraction'),
                                    ('*', 'multiplication'), ('/', 'division')]
              if not any(op in s for s in sols)]
    if len(unused) == 1:
        return c('dgray', f'no {unused[0]} is used')
    if not unused:
        return c('dgray', 'no hint available')
    # multiple unused — report the most surprising one
    for op, name in [('/', 'division'), ('-', 'subtraction'), ('+', 'addition')]:
        if name in unused:
            return c('dgray', f'no {name} is used')
    return c('dgray', 'no hint available')

# ── expression validator ──────────────────────────────────────────────────────

_SAFE = (ast.Expression, ast.BinOp, ast.UnaryOp, ast.Constant,
         ast.Add, ast.Sub, ast.Mult, ast.Div, ast.USub, ast.UAdd)

def validate_expr(raw, numbers, target):
    """Returns (ok, result_or_None, error_or_None)."""
    expr = raw.strip().replace('×', '*').replace('÷', '/').replace('x', '*')
    expr = _expand_implied_mul(expr)
    if re.search(r'[^0-9+\-*/() .]', expr):
        bad = re.search(r'[^0-9+\-*/() .]', expr).group()
        return False, None, f"invalid char '{bad}'"
    used = [int(x) for x in re.findall(r'\d+', expr)]
    if sorted(used) != sorted(numbers):
        return False, None, f"use exactly  {numbers}"
    try:
        tree = ast.parse(expr, mode='eval')
        for node in ast.walk(tree):
            if not isinstance(node, _SAFE):
                return False, None, "unsupported operation"
        result = float(eval(compile(tree, '<expr>', 'eval')))
        return True, result, None
    except ZeroDivisionError:
        return False, None, "division by zero"
    except:
        return False, None, "invalid expression"

# ── puzzle display ────────────────────────────────────────────────────────────
#
# Layout with N prev_lines:
#
#   rows 1..N   history entry (summary + solutions)
#   row  N+1    blank spacer  (or row 1 blank if no history)
#   row  N+2    #puzzle_num
#   row  N+3    (blank → overwritten by LiveTimer)   ← timer_row = N+3
#   row  N+4    (blank)
#   row  N+5    ─────────────────────────────
#   row  N+6    (blank)
#   row  N+7    numbers
#   row  N+8    (blank)
#   row  N+9    ─── target ───
#   row  N+10   (blank)
#   row  N+11   ●●○○  difficulty
#   row  N+12   (blank)
#   row  N+13   ─────────────────────────────
#   row  N+14   (blank)
#   row  N+15   [i]nfo  [h]int  [skip] ...
#   row  N+16   (blank)
#   row  N+17   ›  prompt

def draw_puzzle(puzzle_num, nums, target, difficulty, extra_lines=None, prev_lines=None):
    clear()
    dc   = DIFF_COLORS.get(difficulty, 'gray')
    dots = DIFF_DOTS.get(difficulty, '●●●○')

    visible = _clip_history(prev_lines) if prev_lines else []
    if visible:
        for line in visible:
            print(line)                                                  # rows 1..N (seps included)
    else:
        print()                                                          # blank row 1
    print(c('dgray', f'  #{puzzle_num}'))                               # row N+1  ← number only
    print()                                                              # row N+2  ← TIMER
    timer_row = (len(visible) + 2) if visible else 3
    print()                                                              # row 4
    print(hr())                                                          # row 5
    print()                                                              # row 6
    print(center('   '.join(c('white', str(n), b=True) for n in nums))) # row 7
    print()                                                              # row 8
    print(center(c('dgray','─── ') + c('cyan',str(target),b=True) + c('dgray',' ───')))  # row 9
    print()                                                              # row 10
    print(center(c(dc, dots) + '  ' + c(dc, difficulty)))              # row 11
    print()                                                              # row 12
    print(hr())                                                          # row 13
    print()                                                              # row 14
    if extra_lines:
        for line in extra_lines:
            print(center(line))
        print()
    print(center(c('dgray', '[i]nfo  [h]int  [skip]  [log]  [q]uit')))
    print()
    # next row: written by prompt_input()
    return timer_row

def prompt_input(on_resize=None):
    """Read a line, recentering the prompt+text after every keystroke."""
    if _resize_flag.is_set():
        _resize_flag.clear()
        if on_resize: on_resize()

    buf = []
    fd  = sys.stdin.fileno()

    def _redraw_input():
        text   = ''.join(buf)
        visual = c('teal', '  ›  ') + (c('white', text) if text else '')
        sys.stdout.write('\r\033[K' + center(visual))
        sys.stdout.flush()

    if not _HAS_TTY:
        # Non-TTY fallback (e.g. piped input)
        _redraw_input()
        try:    return input()
        except (KeyboardInterrupt, EOFError): return None

    try:
        old = termios.tcgetattr(fd)
    except Exception:
        _redraw_input()
        try:    return input()
        except (KeyboardInterrupt, EOFError): return None

    try:
        _tty.setcbreak(fd)
        _redraw_input()
        while True:
            # Poll so resize events are handled even without a keypress
            ready, _, _ = select.select([fd], [], [], 0.1)
            if _resize_flag.is_set():
                _resize_flag.clear()
                if on_resize: on_resize()
                _redraw_input()
                continue
            if not ready:
                continue
            b  = os.read(fd, 1)
            ch = b.decode('utf-8', errors='ignore')
            if ch in ('\r', '\n'):
                sys.stdout.write('\n'); sys.stdout.flush()
                return ''.join(buf)
            elif ch == '\x03': raise KeyboardInterrupt
            elif ch == '\x04': raise EOFError
            elif ch in ('\x7f', '\x08'):          # backspace / ^H
                if buf: buf.pop()
            elif ch == '\x1b':                     # escape sequence — consume & skip
                r2, _, _ = select.select([fd], [], [], 0.05)
                if r2: os.read(fd, 4)
                continue
            elif ch >= ' ':
                buf.append(ch)
            _redraw_input()
    except (KeyboardInterrupt, EOFError):
        sys.stdout.write('\n'); sys.stdout.flush()
        return None
    finally:
        try: termios.tcsetattr(fd, termios.TCSADRAIN, old)
        except Exception: pass

# ── session log ───────────────────────────────────────────────────────────────

# Layout constants
_LOG_IND  = '  '
_LOG_N_W  = 4       # "#N  " — up to puzzle #9999
_LOG_GAP  = '  '
_LOG_SUB  = _LOG_IND + ' ' * _LOG_N_W + _LOG_GAP   # 8-char indent for sub-lines
_LOG_LPAD = 11      # label column width inside sub-lines

def _log_sep():
    return _LOG_IND + P['dgray'] + '─' * (term_w() - len(_LOG_IND)) + RST


def _nm_w(log):
    """Width of the numbers column: widest entry or a sensible default."""
    if not log:
        return 10
    return max(len('  '.join(str(n) for n in e['nums'])) for e in log)


def _format_entry(entry, idx, nm_w=None):
    """Return a list of display lines for one log entry (summary + solutions).
    Used by both show_log() and the history bar above each new puzzle."""
    IND, N_W, GAP = _LOG_IND, _LOG_N_W, _LOG_GAP
    SUB, LPAD     = _LOG_SUB, _LOG_LPAD

    dc     = DIFF_COLORS.get(entry.get('dlabel', 'medium'), 'dgray')
    dlbl   = entry.get('dlabel', '?')
    dots   = DIFF_DOTS.get(dlbl, '●○○○')
    nm_str = '  '.join(str(n) for n in entry['nums'])
    NM_W   = nm_w if nm_w is not None else len(nm_str)
    n_col  = c('dgray', f'#{idx + 1:<{N_W - 1}}')
    nm_col = c('white', f'{nm_str:<{NM_W}}', b=True)
    tg_col = c('cyan',  str(entry['target']), b=True)
    dc_col = c(dc, dots + '  ' + dlbl)

    left  = f"{IND}{n_col}{GAP}{nm_col}  →  {tg_col}"

    if entry['status'] == 'solved':
        right = c('white', f"{entry['time']:.2f} s", b=True) + '  ' + c('green', '✓')
    else:
        right = c('dgray', 'skipped') + '  ' + c('dgray', '↷')

    pad     = max(2, term_w() - vlen(left) - vlen(right))
    summary = left + ' ' * pad + right
    lines   = [summary]

    # ── solutions + difficulty on the same line where possible ────────────────
    # Difficulty floats right on the solutions line; solutions wrap below if needed.
    submitted = entry.get('submitted')
    sols      = entry.get('solutions', [])

    lbl       = f'{"solutions":<{LPAD}}'
    prefix_w  = len(SUB) + LPAD
    sep_plain = '  ·  '
    sep_col   = c('dgray', sep_plain)
    indent    = SUB + ' ' * LPAD
    dc_w      = vlen(dc_col)
    gap       = 3   # spaces between last solution and difficulty

    # Width available for solutions on the first (shared) line vs continuation lines
    avail_first = term_w() - prefix_w - gap - dc_w
    avail_rest  = term_w() - prefix_w

    if sols or submitted:
        if submitted and submitted in sols:
            ordered = [submitted] + [s for s in sols if s != submitted]
        elif submitted:
            ordered = [submitted] + sols
        else:
            ordered = sols

        def _col(i, s):
            d = _display_sol(s)
            return c('green', d) if i == 0 and submitted else c('dgray', d)

        sol_lines, cur, cur_w, first = [], [], 0, True
        for i, s in enumerate(ordered):
            col   = _col(i, s)
            pw    = len(strip_ansi(col)) + (len(sep_plain) if cur else 0)
            avail = avail_first if first else avail_rest
            if cur and cur_w + pw > avail:
                sol_lines.append((sep_col.join(cur), first))
                cur, cur_w, first = [col], len(strip_ansi(col)), False
            else:
                cur.append(col); cur_w += pw
        if cur:
            sol_lines.append((sep_col.join(cur), first))

        for j, (sl, is_first) in enumerate(sol_lines):
            pfx = f"{SUB}{c('dgray', lbl)}" if j == 0 else indent
            if is_first:
                # Right-align difficulty on this line
                sol_w = prefix_w + len(strip_ansi(sl))
                dp    = max(gap, term_w() - sol_w - dc_w)
                lines.append(pfx + sl + ' ' * dp + dc_col)
            else:
                lines.append(pfx + sl)
    else:
        # No solutions — difficulty on its own line, right-aligned
        dp = max(0, term_w() - len(IND) - dc_w)
        lines.append(IND + ' ' * dp + dc_col)

    return lines


def show_log(log):
    clear()
    print()
    print(center(c('cyan', 'session log', b=True)))
    print()

    if not log:
        print(center(c('dgray', 'nothing yet')))
        print()
        return

    sep      = _log_sep()
    col_nm_w = _nm_w(log)

    solved_count = 0
    total_time   = 0.0

    for i, e in enumerate(log):
        print(sep)
        for line in _format_entry(e, i, nm_w=col_nm_w):
            print(line)
        if e['status'] == 'solved':
            solved_count += 1
            total_time   += e['time']

    print(sep)
    print()

    avg_str  = f'{total_time / solved_count:.2f} s' if solved_count else '─'
    left     = _LOG_SUB + c('dgray', 'solved ') + c('white', f'{solved_count}/{len(log)}', b=True)
    right    = c('dgray', 'avg ') + c('white', avg_str)
    pad      = max(2, term_w() - vlen(left) - vlen(right))
    print(left + ' ' * pad + right)
    print()

# ── title / help ──────────────────────────────────────────────────────────────

TITLE_ART = [
    "   _     ___     _     ＿＿    _     ＿   ",
    "  /_\   | _ )   /_\   / __/   /_\   | |   ",
    " / _ \  | _ \  / _ \ ｜ \__  / _ \  | |__ ",
    "/_/ \_\ |___/ /_/ \_\ \___/ /_/ \_\ |＿＿|",
]

def show_title():
    clear()
    print(); print()
    for line in TITLE_ART:
        print(center(c('cyan', line, b=True)))
    print()
    print(center(c('dgray', 'the number puzzle')))
    print(); print()
    print(center(c('dgray', 'use all numbers with  ') +
                 c('yellow', '+  −  ×  ÷') +
                 c('dgray', '  to reach the target')))
    print()

def show_how_to_play():
    clear(); print(); print()
    print(center(c('cyan', 'how to play', b=True)))
    print()
    rules = [
        ('numbers', f"given numbers        e.g.  {c('yellow', '3   7   4')}"),
        ('target',  f"and a target         e.g.  {c('cyan', '25', b=True)}"),
        ('goal',    f"combine all numbers to reach the target"),
        ('ops',     f"use  {c('yellow', '+  −  *  /')}  and  {c('yellow', '( )')}  in any order"),
        ('once',    f"each number exactly once"),
        ('',        ''),
        ('example', f"{c('dgray', '3 * 7 + 4  =  25')}  {c('green', '✓')}"),
        ('',        ''),
        ('i',       f"type  {c('teal', 'i')}     to toggle solution count"),
        ('h',       f"type  {c('teal', 'h')}     to toggle a hint"),
        ('skip',    f"type  {c('teal', 'skip')}  to skip"),
        ('log',     f"type  {c('teal', 'log')}   to view session log"),
        ('quit',    f"type  {c('teal', 'q')}  or  {c('teal', 'quit')}  to finish"),
    ]
    # Block-center: compute shared indent from widest rendered row
    rendered = []
    for key, val in rules:
        if not key and not val:
            rendered.append(None)
            continue
        k = c('teal', f'{key:<8}') if key else ' ' * 8
        rendered.append(k + '  ' + val)

    pad = ' ' * max(0, (term_w() - max(vlen(r) for r in rendered if r)) // 2)
    for row in rendered:
        print() if row is None else print(pad + row)
    print()
    print(pad + c('dgray', 'press enter'))
    try: input()
    except (KeyboardInterrupt, EOFError): pass

# ── difficulty picker ─────────────────────────────────────────────────────────

DIFF_ALIASES = {
    'e': 'easy', 'm': 'medium', 'h': 'hard', 'x': 'expert',
    'easy': 'easy', 'medium': 'medium', 'hard': 'hard', 'expert': 'expert',
}

DIFF_DESCS = {
    'easy':   '4 numbers    ·  small puzzles',
    'medium': '4-5 numbers  ·  moderate puzzles',
    'hard':   '5 numbers    ·  tricky puzzles',
    'expert': '6 numbers    ·  hardest puzzles',
}

def pick_difficulty():
    def _draw():
        show_title()
        # Build lines first, then block-center them all with the same indent
        rows = []
        for key, name in [('e','easy'), ('m','medium'), ('h','hard'), ('x','expert')]:
            dc  = DIFF_COLORS[name]
            row = (c('cyan',  f'[{key}]') + '  ' +
                   c(dc,      f'{name:<8}', b=True) + '  ' +
                   c(dc,      DIFF_DOTS[name]) + '  ' +
                   c('dgray', DIFF_DESCS[name]))
            rows.append(row)
        footer = c('dgray', '[?] how to play    [q] quit')

        pad = ' ' * max(0, (term_w() - max(vlen(r) for r in rows + [footer])) // 2)
        for row in rows:
            print(pad + row)
        print()
        print(pad + footer)
        print()

    while True:
        _draw()
        raw = prompt_input(on_resize=_draw)
        if raw is None: return None
        ch = raw.strip().lower()
        if ch in ('q', 'quit'): return None
        if ch == '?':
            show_how_to_play()
            continue
        if ch in DIFF_ALIASES:
            return DIFF_ALIASES[ch]

# ── game loop ─────────────────────────────────────────────────────────────────

def _between_rounds_prompt(difficulty, prev_lines=None):
    """Full-screen between-rounds view: history + colored difficulty picker."""
    def _draw():
        clear()
        if prev_lines:
            for ln in prev_lines:
                print(ln)
        print()
        rows = []
        for key, name in [('e','easy'), ('m','medium'), ('h','hard'), ('x','expert')]:
            dc  = DIFF_COLORS[name]
            row = (c('cyan',  f'[{key}]') + '  ' +
                   c(dc,      f'{name:<8}', b=True) + '  ' +
                   c(dc,      DIFF_DOTS[name]) + '  ' +
                   c('dgray', DIFF_DESCS[name]))
            rows.append(row)
        footer = c('dgray', '[enter] next   [q] quit')
        pad = ' ' * max(0, (term_w() - max(vlen(r) for r in rows + [footer])) // 2)
        for row in rows:
            print(pad + row)
        print()
        print(pad + footer)
        print()

    while True:
        _draw()
        raw = prompt_input(on_resize=_draw)
        if raw is None: return None
        ch = raw.strip().lower()
        if ch in ('q', 'quit'): return None
        if ch == '': return difficulty
        if ch in DIFF_ALIASES: return DIFF_ALIASES[ch]


def _build_history_lines(log):
    """Build the fully-formatted history block (seps + entries) for all completed puzzles."""
    if not log:
        return []
    sep      = _log_sep()
    col_nm_w = _nm_w(log)
    lines    = []
    for i, e in enumerate(log):
        lines.append(sep)
        lines.extend(_format_entry(e, i, nm_w=col_nm_w))
    lines.append(sep)
    return lines


def play(difficulty):
    log          = []
    puzzle_n     = 0
    timer        = LiveTimer()
    prev_lines   = []   # fully-formatted history block for all completed puzzles

    while True:
        puzzle_n += 1
        timer.reset()

        clear()
        visible = _clip_history(prev_lines)
        if visible:
            for ln in visible: print(ln)
        else:
            print()
        print(center(c('dgray', 'generating...')))
        timer.timer_row = (len(visible) + 2) if visible else 3

        nums, target, sols, dlabel = generate_puzzle(difficulty)
        info_text  = build_puzzle_info(sols, len(sols))
        hint_text  = generate_hint(sols, nums, target)
        show_info  = [False]   # mutable so closures can toggle
        show_hint  = [False]

        def _redraw():
            extra = []
            if show_info[0]: extra.append(info_text)
            if show_hint[0]: extra.append(hint_text)
            # Rebuild + clip history at current terminal size (handles resize correctly)
            timer.timer_row = draw_puzzle(puzzle_n, nums, target, difficulty,
                                          extra_lines=extra if extra else None,
                                          prev_lines=_build_history_lines(log))

        timer.redraw_fn = _redraw
        timer.timer_row = draw_puzzle(puzzle_n, nums, target, difficulty,
                                      prev_lines=prev_lines)
        timer.start()

        action = None   # 'quit' | 'next'
        while True:
            raw = prompt_input(on_resize=_redraw)
            timer.stop()   # halt display thread while we process

            if raw is None or raw.strip().lower() in ('q', 'quit'):
                action = 'quit'
                break

            cmd = raw.strip().lower()

            if cmd == 'i':
                show_info[0] = not show_info[0]
                _redraw()
                timer.start()
                continue

            if cmd == 'h':
                show_hint[0] = not show_hint[0]
                _redraw()
                timer.start()
                continue

            if cmd == 'skip':
                log.append({'nums': nums, 'target': target, 'time': None,
                            'status': 'skipped', 'submitted': None,
                            'solutions': sols, 'n_sols': len(sols),
                            'dlabel': difficulty})
                action = 'next'
                break

            if cmd == 'log':
                show_log(log)
                print(center(c('dgray', 'press enter to continue')))
                try: input()
                except: pass
                _redraw()
                timer.start()
                continue

            if not raw.strip():
                timer.start()
                continue

            ok, result, err = validate_expr(raw, nums, target)

            if not ok:
                print()
                print(center(c('red', f'✗  {err}')))
                time.sleep(1.5)
                _redraw()
                timer.start()
                continue

            if abs(result - target) < 1e-9:
                elapsed    = round(time.time() - timer.t0, 2)
                canonical  = _canonicalize_user_expr(raw)
                submitted  = canonical if canonical in sols else re.sub(r'\s+', '', raw.strip())
                log.append({'nums': nums, 'target': target, 'time': elapsed,
                            'status': 'solved', 'submitted': submitted,
                            'solutions': sols, 'n_sols': len(sols),
                            'dlabel': difficulty})
                action = 'next'
                break
            else:
                print()
                print(center(c('red', f'✗  {result:.5g}  ≠  {target}')))
                time.sleep(1.5)
                _redraw()
                timer.start()

        def _show_end():
            save_session(log, difficulty)
            show_log(log)
            print(center(c('dgray', 'press enter')))
            try: input()
            except: pass

        if action == 'quit':
            _show_end()
            return

        # Rebuild full history block for all completed puzzles
        prev_lines = _build_history_lines(log)

        # Between rounds
        new_diff = _between_rounds_prompt(difficulty, prev_lines)
        if new_diff is None:
            _show_end()
            return
        difficulty = new_diff

# ── entry point ───────────────────────────────────────────────────────────────

def parse_args():
    ap = argparse.ArgumentParser(
        prog='abacal',
        description='ABACAL — the number puzzle',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='\n'.join([
            'difficulty:',
            '  easy    4 numbers, small targets',
            '  medium  4-5 numbers, moderate targets',
            '  hard    5 numbers, tricky targets',
            '  expert  6 numbers, hardest targets',
            '',
            'examples:',
            '  abacal               interactive difficulty picker',
            '  abacal -d medium     jump straight in',
            '  abacal hard          shorthand positional arg',
        ])
    )
    ap.add_argument('diff_pos', nargs='?',
                    choices=['easy', 'medium', 'hard', 'expert',
                             'e', 'm', 'h', 'x'],
                    metavar='DIFFICULTY',
                    help='difficulty as positional arg (easy/medium/hard/expert or e/m/h/x)')
    ap.add_argument('--difficulty', '-d',
                    choices=['easy', 'medium', 'hard', 'expert'],
                    default=None, metavar='DIFF',
                    help='difficulty level')
    return ap.parse_args()

def main():
    signal.signal(signal.SIGINT,   lambda *_: (print(), sys.exit(0)))
    signal.signal(signal.SIGWINCH, _sigwinch)

    args = parse_args()

    # resolve difficulty from positional or flag
    diff = args.difficulty
    if diff is None and args.diff_pos:
        diff = DIFF_ALIASES.get(args.diff_pos, args.diff_pos)

    if diff is None:
        diff = pick_difficulty()

    if diff is None:
        clear()
        print()
        print(center(c('dgray', 'thanks for playing!')))
        print()
        return

    play(diff)

    clear()
    print()
    print(center(c('dgray', 'thanks for playing!')))
    print()

if __name__ == '__main__':
    main()
