"""Plain-definition ordinals with context-free tail splitting.

For X = P⌢T, one expansion step of X is *local to T* when every ancestor
a_1..a_br used by the bad-root search lies in T.  Suffixes that start in T
lie wholly in T, so sp, mbp and the stop test then read only T: the step
is the same for every P, and the expansion is P ⌢ (G_T ⌢ B^n).

h(T) = order type of T's descent while every step stays local
       (None as soon as one step would look into P).
Then o(P⌢T) = o(P) + h(T).  Both o and h use the same guessed sup
(evalord.sup) over n = 1..3, so values equal those of evalord.o.
"""
import sys
import ssos
from ssos import suffix_ranks
from ordinal import ZERO, succ, add, show
from evalord import sup, Unknown

sys.setrecursionlimit(1000000)
NS = (1, 2, 3)
memo_o, memo_h = {}, {}


class Escape(Exception):
    pass


def local_parts(T):
    """(G_T, B) of the expansion of P⌢T when local to T, else raise Escape."""
    L = len(T)
    rk = [0] + suffix_ranks(T) + [-1]

    def sp(x):
        for i in range(x - 1, 0, -1):
            if rk[i] < rk[x]:
                return i
        raise Escape

    def mbp(x):
        cand = [i for i in range(x, L) if T[i - 1] < T[L - 1]]
        return max(cand, key=lambda i: rk[i + 1]) if cand else L - 1

    p = [L]
    pbp = [None]

    def P(i):
        while len(p) <= i:
            p.append(sp(p[-1]))
            pbp.append(None)
        if pbp[i] is None:
            pbp[i] = mbp(p[i])
        return pbp[i]

    i = 2
    while True:
        a, b = rk[P(i)], rk[P(i - 1)]
        if a <= b or rk[P(i) + 1] <= rk[P(i - 1) + 1]:
            break
        i += 1
    cut = P(i)
    return T[:cut], T[cut:-1] + (T[-1] - 1,), p[i]


def h(T):
    """order type of T's local descent, or None if it escapes."""
    if T in memo_h:
        return memo_h[T]
    if not T:
        r = ZERO
    elif T[-1] == 0:
        r0 = h(T[:-1])
        r = None if r0 is None else succ(r0)
    else:
        try:
            G, B, a = local_parts(T)
        except Escape:
            memo_h[T] = None
            return None
        r = None
        if a > 1:  # the step reads only T[a-1:], so split there
            hu, hv = h(T[:a - 1]), h(T[a - 1:])
            if hu is not None and hv is not None:
                r = add(hu, hv)
        if r is None:
            xs = []
            for n in NS:
                v = h(G + B * n)
                if v is None:
                    memo_h[T] = None
                    return None
                xs.append(v)
            r = sup(xs)
            if r is None:
                raise Unknown((T, [show(x) for x in xs]))
    memo_h[T] = r
    return r


def o(S):
    S = tuple(S)
    if S in memo_o:
        return memo_o[S]
    if not S:
        r = ZERO
    elif S[-1] == 0:
        r = succ(o(S[:-1]))
    else:
        q = ssos.Seq(S)
        G, B = ssos.parts(S)
        a = q.p(q.br())          # leftmost ancestor read by this step
        r = None
        if a > 1:
            ht = h(S[a - 1:])
            if ht is not None:
                r = add(o(S[:a - 1]), ht)
        if r is None:
            xs = [o(G + B * n) for n in NS]
            r = sup(xs)
            if r is None:
                raise Unknown((S, [show(x) for x in xs]))
    memo_o[S] = r
    return r
