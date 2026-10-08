"""Hypothesis: a self-referential block u = 2 ⌢ (f(x_1) ⌢ ... ⌢ f(x_m)) with
f(0) = (0,1,2), f(1) = (0,2), f(2) = (1) has value ε_ι, ι = -2 + o((0,0,x_1,...,x_m))."""
import hyb, conj2
from ordinal import P, ONE, ZERO, show
F = {0: (0, 1, 2), 1: (0, 2), 2: (1,)}
def lower(u):
    u = tuple(u)
    if not u or u[0] != 2: return None
    rest = u[1:]; out = []
    while rest:
        for x, pat in sorted(F.items(), key=lambda kv: -len(kv[1])):
            if rest[:len(pat)] == pat:
                out.append(x); rest = rest[len(pat):]; break
        else:
            return None
    return tuple(out)
def minus2(x):
    # -2 + x for x infinite is x; for finite x = n it is n - 2
    from ordinal import ONE as O
    if x and all(t == O[0] for t in x): return x[:-2] if len(x) >= 2 else ()
    return x
ACTIVE = set()
def hook(u):
    u = tuple(u)
    L = lower(u)
    if L is None or (0, 0) + L in ACTIVE or (0, 0) + L >= (0, 0) + u:
        return fallback(u)
    ACTIVE.add((0, 0) + L)
    try:
        idx = minus2(hyb.o((0, 0) + L))
    finally:
        ACTIVE.discard((0, 0) + L)
    return P(ONE, idx)
def fallback(u):
    S = (0, 0) + u
    if S in ACTIVE: return None
    ACTIVE.add(S)
    try: return hyb._hook(u)
    finally: ACTIVE.discard(S)
