"""Assign ordinals to 強2階探索数列 by o(S⌢0) = o(S)+1 and
o(S) = sup_n o(G⌢B^n) for limit S.

The sup is found by guessing candidates from the shape of the terms
(common prefix, growing multiplicity, growing head, nesting -> next fixed
point) and keeping the least candidate a that passes
    x_n < a for all n,  and  a[k] <= x_last for k = 1..K
with the standard Veblen fundamental sequences a[k].
"""
import sys
import ssos
from ordinal import (ZERO, ONE, P, w, add, succ, cmp, lt, fs, is_limit,
                     show)

sys.setrecursionlimit(100000)

NS = (2, 3, 4, 5)


def groups(x):
    g = []
    for t in x:
        if g and g[-1][0] == t:
            g[-1][1] += 1
        else:
            g.append([t, 1])
    return [(t, c) for t, c in g]


def ungroup(gs):
    out = ()
    for t, c in gs:
        out += (t,) * c
    return out


def next_fp(c, x):
    """least phi(c, d) > x"""
    base = P(c, ZERO)
    if lt(x, base):
        return base
    p = x[0]
    _, e, f = p
    ce = cmp(e, c)
    if ce == 0:
        return P(c, succ(f))
    if ce > 0:
        return P(c, succ((p,)))
    return next_fp(c, f)


def exponent(t):
    _, a, b = t
    return b if not a else (t,)


def sup_cands(xs, depth=0):
    out = set()
    if depth > 40 or len(xs) < 2:
        return out
    for j in range(0, len(xs) - 1):
        ys = xs[j:]
        if any(not lt(ys[i], ys[i + 1]) for i in range(len(ys) - 1)):
            continue
        gs = [groups(y) for y in ys]
        i = 0
        while all(i < len(g) for g in gs) and all(g[i] == gs[0][i] for g in gs):
            i += 1
        pre = ungroup(gs[0][:i])
        items = [g[i] if i < len(g) else None for g in gs]
        if all(it is not None for it in items) and all(it[0] == items[0][0] for it in items):
            e = exponent(items[0][0])
            out.add(add(pre, w(succ(e))))
            continue
        heads = [(it[0],) for it in items if it is not None]
        for L in sup_principal_cands(heads, depth + 1):
            out.add(add(pre, L))
    return out


def sup_principal_cands(hs, depth):
    out = set()
    if len(hs) < 2:
        return out
    As = [h[0][1] for h in hs]
    Bs = [h[0][2] for h in hs]
    if all(a == As[0] for a in As):
        a = As[0]
        for B in sup_cands(Bs, depth):
            out.add(P(a, B))
        out.add(next_fp(succ(a), hs[0]))
    else:
        for A in sup_cands(As, depth):
            out.add(P(A, ZERO))
    top = max(As, key=lambda a: (len(a), a))  # any; refined below
    for a in As:
        if all(cmp(a, b) >= 0 for b in As):
            top = a
    out.add(next_fp(succ(top), hs[0]))
    return out


def check(a, xs, K):
    if not is_limit(a):
        return False
    if not all(lt(x, a) for x in xs):
        return False
    for k in range(1, K + 1):
        if lt(xs[-1], fs(a, k)):
            return False
    return True


def sup(xs):
    cands = sorted(sup_cands(xs), key=_Key)
    K = len(xs) - 1
    for a in cands:
        if check(a, xs, K):
            return a
    return None


class _Key:
    def __init__(self, x):
        self.x = x

    def __lt__(self, o):
        return cmp(self.x, o.x) < 0


class Unknown(Exception):
    pass


memo = {}


def o(S):
    S = tuple(S)
    if S in memo:
        return memo[S]
    if not S:
        r = ZERO
    elif S[-1] == 0:
        r = succ(o(S[:-1]))
    else:
        xs = [o(ssos.fs(S, n)) for n in NS]
        r = sup(xs)
        if r is None:
            raise Unknown((S, [show(x) for x in xs]))
    memo[S] = r
    return r


if __name__ == "__main__":
    for arg in sys.argv[1:]:
        S = tuple(int(x) for x in arg.split(","))
        print(S, show(o(S)))
