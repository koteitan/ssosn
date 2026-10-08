"""Ordinals below the large Veblen-free range, in Cantor/Veblen normal form.

An ordinal is a tuple of principal terms in non-increasing order (0 = ()).
A principal term is ('p', a, b) meaning phi(a, b); omega^b = phi(0, b).
Terms are kept normal: phi(a, phi(c, d)) with c > a collapses to phi(c, d).
"""
import re
from functools import lru_cache

ZERO = ()


def P(a, b):
    """phi(a, b) as an ordinal (normalized)."""
    if len(b) == 1 and cmp(b[0][1], a) > 0:  # b = phi(c,d), c > a: fixed point
        return b
    return (('p', a, b),)


ONE = (('p', ZERO, ZERO),)
OMEGA = (('p', ZERO, ONE),)


def nat(n):
    return ONE * n


def w(b):
    return P(ZERO, b)


@lru_cache(maxsize=None)
def cmp_p(p, q):
    if p == q:
        return 0
    _, a, b = p
    _, c, d = q
    ca = cmp(a, c)
    if ca == 0:
        return cmp(b, d)
    if ca < 0:  # p < q iff b < q
        return -1 if cmp(b, (q,)) < 0 else 1
    # a > c: q < p iff d < p
    return 1 if cmp(d, (p,)) < 0 else -1


@lru_cache(maxsize=None)
def cmp(x, y):
    for s, t in zip(x, y):
        c = cmp_p(s, t)
        if c:
            return c
    return (len(x) > len(y)) - (len(x) < len(y))


def lt(x, y):
    return cmp(x, y) < 0


def add(x, y):
    if not y:
        return x
    h = y[0]
    k = len(x)
    while k > 0 and cmp_p(x[k - 1], h) < 0:
        k -= 1
    return x[:k] + y


def succ(x):
    return add(x, ONE)


def is_limit(x):
    return bool(x) and x[-1] != ONE[0]


def pred(x):
    assert x and x[-1] == ONE[0]
    return x[:-1]


@lru_cache(maxsize=None)
def fs(x, k):
    """Standard fundamental sequence x[k] (k >= 1) for limit x."""
    assert is_limit(x), x
    pre, t = x[:-1], x[-1]
    return add(pre, fs_p(t, k))


def fs_p(t, k):
    _, a, b = t
    if not a:  # omega^b
        if b and b[-1] == ONE[0]:
            return w(pred(b)) * k
        return w(fs(b, k))
    if b and is_limit(b):
        return P(a, fs(b, k))
    # b = 0 or successor
    start = succ(P(a, pred(b))) if b else ZERO
    if a[-1] == ONE[0]:  # a successor: iterate phi(a-1, .)
        a1 = pred(a)
        y = start
        for _ in range(k):
            y = P(a1, y)
        return y
    return P(fs(a, k), start)


# ---------------------------------------------------------------- printing
# Sugar as the user prefers: w = omega, e0 = epsilon_0, z0 = zeta_0.

def _top(s, chars):
    d = 0
    for ch in s:
        if ch in "({":
            d += 1
        elif ch in ")}":
            d -= 1
        elif d == 0 and ch in chars:
            return True
    return False


def _wrap(s):
    if _top(s, "+·") or re.fullmatch(r"w\d+", s):
        return "(" + s + ")"
    return s


def show(x):
    if not x:
        return "0"
    out = []
    i = 0
    while i < len(x):
        j = i
        while j < len(x) and x[j] == x[i]:
            j += 1
        c = j - i
        s = show_p(x[i])
        if s == "1":
            s = str(c)
        elif c > 1:
            s = s + str(c) if s == "w" else s + "·" + str(c)
        out.append(s)
        i = j
    return "+".join(out)


def show_p(t):
    _, a, b = t
    if not a:
        if not b:
            return "1"
        if b == ONE:
            return "w"
        return "w^" + _wrap(show(b))
    name = {1: "e", 2: "z", 3: "h"}.get(len(a)) if all(u == ONE[0] for u in a) else None
    if name:
        s = show(b)
        return name + (s if s.isdigit() else "_" + _wrap(s))
    return "phi(" + show(a) + "," + show(b) + ")"
