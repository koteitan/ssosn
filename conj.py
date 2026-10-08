"""Conjectured translation for ./ssosn --fix below (0,0,2) (entries 0/1 after (0,0)).
o((0,0) ⌢ Y) = 2 + v(Y)
v(Y)  = sum, left to right, of units of Y:
        a 0 outside blocks -> 1
        a block B          -> w^(1 + v(T(B)))
        block = maximal 1 (0? 1)*   (1s separated by single 0s; "0,0" ends it)
T(B)  = B with every maximal run 1^a replaced by 1^(a-1) (single 0s kept)."""
from ordinal import ZERO, ONE, add, w, nat, show, lt
import re

def units(Y):
    s = ''.join(map(str, Y)); out = []; i = 0
    while i < len(s):
        if s[i] == '0': out.append('0'); i += 1; continue
        m = re.match(r'1(01|1)*', s[i:])
        out.append(m.group(0)); i += len(m.group(0))
    return out

def T(B):
    return tuple(int(c) for c in re.sub(r'1(1*)', r'\1', B))

def v(Y):
    r = ZERO
    for u in units(Y):
        r = add(r, ONE if u == '0' else w(add(ONE, v(T(u)))))
    return r

def o(S):
    S = tuple(S); assert S[:2] == (0, 0) and set(S[2:]) <= {0, 1}
    return add(nat(2), v(S[2:]))

def rcut_Y(Y):
    """recursive cut inside Y (entries 0/1, last = 1): position (number of entries of Y kept)."""
    s = ''.join(map(str, Y))
    us = units(Y); B = us[-1]; start = len(s) - len(B)
    runs = B.split('0')                      # runs of 1s, each non-empty (block has single 0s)
    t = T(B)
    if not t or t[-1] == 0:
        return start
    q = rcut_Y(t)                            # cut in T(B): lands at the start of a run of T(B)
    # map T-position q to B-position: walk runs of B
    pos_t = pos_b = 0
    for j, r in enumerate(runs):
        if pos_t == q:
            return start + pos_b
        pos_t += len(r) - 1; pos_b += len(r)
        if j < len(runs) - 1:
            pos_t += 1; pos_b += 1           # the single 0
    raise AssertionError((Y, q))

def rcut(S):
    return 2 + rcut_Y(S[2:])
