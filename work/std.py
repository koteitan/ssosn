"""Standard-form test by greedy descent from TOP (uses the 'no gaps' property:
T < S standard implies T <= S[n] for some n, and lexicographic order = ordinal order).
  T := TOP; loop: if T == S: standard.
  T ends in 0: T := T[:-1] if T[:-1] >= S else not standard.
  T limit: T := least T[n] = G⌢B^n with T[n] >= S (none: not standard)."""
import harness
TOP = (0, 0, 3)


def above_all_terms(G, B, S):
    """True if S >= G⌢B^n for every n (S is at or above the lexicographic limit G⌢B^ω)."""
    n = len(S) // len(B) + 2
    lim = G + B * n          # longer than S, agrees with G⌢B^ω on len(S) entries
    return lim[:len(S)] < S     # equal: S is a prefix of a term, hence below it


def descend(S, top=TOP, steps=100000):
    """yield the greedy path from top towards S."""
    S = tuple(S); T = tuple(top)
    for _ in range(steps):
        yield T
        if T == S or T < S or not T: return
        if T[-1] == 0:
            T = T[:-1]; continue
        c = harness.Seq(T, 'new').cut()
        G, B = T[:c], T[c:-1] + (T[-1] - 1,)
        if above_all_terms(G, B, S): return
        n = 1; X = G + B
        while X < S:
            n += 1; X = G + B * n
        T = X


def is_standard(S, top=TOP):
    S = tuple(S); last = None
    for T in descend(S, top):
        last = T
    return last == S


def ceil(X, top=TOP):
    """least standard form >= X (the last node of the greedy descent)."""
    last = None
    for T in descend(X, top):
        if T >= tuple(X): last = T
    return last
