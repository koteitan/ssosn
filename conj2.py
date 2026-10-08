"""Conjectural extension of conj.py to entries {0,1,2} (NOT proved; checked on data).
units: a 0 outside blocks, or a block = maximal run of nonzero entries separated by single 0s.
T(B): in every maximal run of nonzero entries, drop the first entry if it is 1.
value(block B) = w^(1 + v(T(B))); if T(B) == B the block is self-referential:
only B = (2) is handled (value e0); others return None."""
from ordinal import ZERO, ONE, add, w, nat, P
E0 = P(ONE, ZERO)

def units(Y):
    Y = tuple(Y); out = []; i = 0; n = len(Y)
    while i < n:
        if Y[i] == 0: out.append((0,)); i += 1; continue
        j = i
        while j < n and (Y[j] != 0 or (j + 1 < n and Y[j + 1] != 0 and j > i and Y[j - 1] != 0)):
            j += 1
        out.append(Y[i:j]); i = j
    return out

def T(B):
    runs, cur = [], []
    for x in B:
        if x == 0: runs.append(cur); cur = []
        else: cur.append(x)
    runs.append(cur)
    new = [r[1:] if r and all(x == 1 for x in r) else r for r in runs]
    out = []
    for k, r in enumerate(new):
        if k: out.append(0)
        out += r
    return tuple(out)

HOOK = None      # HOOK(u) = value of a self-referential block u (T(u) == u), or None

def v(Y):
    r = ZERO
    for u in units(Y):
        if u == (0,): r = add(r, ONE); continue
        if u == (2,): r = add(r, E0); continue
        t = T(u)
        if t == u:
            x = HOOK(u) if HOOK else None
            if x is None: return None
            r = add(r, x); continue
        x = v(t)
        if x is None: return None
        r = add(r, w(add(ONE, x)))
    return r

def o(S):
    S = tuple(S)
    if S[:2] != (0, 0) or max(S) > 2: return None
    us = units(S[2:])
    if len(us) == 1 and us[0] != (2,) and T(us[0]) == us[0]:
        return None      # S is a single self-referential block: leave it to the recursion
    x = v(S[2:])
    return None if x is None else add(nat(2), x)
