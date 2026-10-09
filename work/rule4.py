"""Valuation with the combinatorial lowering:
  rho(Y) built token by token: u := (0,0,2); u := ceil(u ⌢ F[y])   (F: 0->012, 1->02, 2->1)
  lam(u) = the Y with rho(Y) = u, found greedily (largest token whose ceil stays <= u).
A single self-referential block (0,0)⌢u has value 2 + e_ι with ι = -2 + o((0,0)⌢lam(u))."""
import harness, conj, conj2, std
from ordinal import P, ONE, add, nat, succ, show
F = {0: (0, 1, 2), 1: (0, 2), 2: (1,)}
class NoLower(Exception): pass
def rho(Y):
    u = (0, 0, 2)
    for y in Y: u = std.ceil(u + F[y])
    return u
_lam = {}
def lam(S):
    """S = (0,0)⌢u standard single self-ref block; returns the standard (0,0)⌢Y with rho(Y) = u, or None."""
    S = tuple(S)
    if S in _lam: return _lam[S]
    res = None
    def dfs(v, Y, depth):
        if v == S:
            return Y if std.is_standard((0, 0) + Y) else None
        if depth > 4 * len(S) + 10: return None
        for y in (2, 1, 0):
            w = std.ceil(v + F[y])
            if w is not None and w <= S:
                r = dfs(w, Y + (y,), depth + 1)
                if r is not None: return r
        return None
    Y = dfs((0, 0, 2), (), 0)
    res = None if Y is None else (0, 0) + Y
    _lam[S] = res
    return res
def hook_S(S):
    L = lam(S)
    if L is None or L >= S: return None      # no lowering, or not lower: fixed point territory
    x = R(L)
    if x is None: return None
    from lower import minus2
    return P(ONE, minus2(x))
memo = {}
def single_selfref(S):
    us = conj2.units(S[2:])
    return len(us) == 1 and us[0] != (2,) and conj2.T(us[0]) == us[0]
def hook(u):
    u = tuple(u)
    if u == (2,): return P(ONE, ())
    return hook_S((0, 0) + u)
def R(S):
    S = tuple(S)
    if S in memo: return memo[S]
    if S[:2] != (0, 0): r = None
    elif len(S) == 2: r = nat(2)
    elif S[-1] == 0: r = None if (x := R(S[:-1])) is None else succ(x)
    elif max(S) <= 1: r = conj.o(S)
    elif max(S) > 2: r = None
    else:
        conj2.HOOK = hook
        if single_selfref(S):
            x = hook(S[2:]); r = None if x is None else add(nat(2), x)
        else:
            x = conj2.v(S[2:]); r = None if x is None else add(nat(2), x)
    memo[S] = r
    return r
