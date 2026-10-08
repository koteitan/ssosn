"""Candidate corrections of the v3 bad-root search, compared with v2.

seg:   PBP(i) uses the best root in the NEW segment [p(i), p(i-1))
       (i = 1: [p(1), L)), so it can decrease; stop at the first i where
       PBP(i) <= PBP(i-1) or the bad part does not grow.
cut:   'prev' -> G ends at pbp(br-1) (last improving candidate)
       'br'   -> G ends at pbp(br)
"""
import ssos, sos2
from ssos import suffix_ranks


def parts(S, seg=True, cut="prev"):
    S = tuple(S); L = len(S)
    q = ssos.Seq(S); rk = q.rank

    def best(lo, hi):
        c = [i for i in range(lo, hi) if S[i - 1] < S[-1]]
        return max(c, key=lambda i: rk[i + 1]) if c else None

    def pbp(i):
        hi = L if (i == 1 or not seg) else q.p(i - 1)
        b = best(q.p(i), hi)
        return b

    prev = pbp(1)
    if prev is None:
        prev = L - 1
    i = 2
    chosen = prev
    while i <= L:
        cur = pbp(i)
        if cur is None or rk[cur] <= rk[prev] or rk[cur + 1] <= rk[prev + 1]:
            chosen = prev if cut == "prev" else (cur if cur is not None else prev)
            break
        prev = cur
        i += 1
    else:
        chosen = prev
    return S[:chosen], S[chosen:-1] + (S[-1] - 1,)


def fs(S, n, **kw):
    G, B = parts(S, **kw)
    return G + B * n
