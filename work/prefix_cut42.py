"""§42 checks for the prefix cut after A_d and the additive value rule ADD.

1. raw:  fs(Z ++ A_d ++ X, n) == Z ++ fs(A_d ++ X, n) for token words X over
         {A_j (j >= d), W, E, D}, X not starting with D, and (d >= 1) X not ending with A_d.
2. ADD:  F(Z A0 X) == F(Z A0) + F(X) on every pair of decided F values in the §39 tail cache.
usage: python3 work/prefix_cut42.py
"""
import itertools
import os
import sys

sys.path[:0] = [os.path.dirname(os.path.abspath(__file__)),
                os.path.dirname(os.path.dirname(os.path.abspath(__file__)))]

import harness
import pure_s39 as runner
import tail_symbolic as S
from ordinal import add, cmp


def A(k):
    return (0, 1, 2) + (0, 2) * k


TOK = {'A0': A(0), 'A1': A(1), 'A2': A(2), 'A3': A(3), 'A4': A(4),
       'W': (0, 1, 2, 1), 'D': (0, 2), 'E': (0, 1, 2, 0, 2, 1)}
PREFIXES = [(), (0,), (0, 3, 1), (0, 1, 2, 1, 0, 2), (0, 0, 2, 1, 0, 2, 0, 2),
            (0, 0, 2, 1, 0, 2, 0, 1, 2, 1, 0, 2, 1, 0, 1, 2, 0, 2)]


def raw_check(d, max_tokens):
    allowed = [t for t in TOK if not (t[0] == 'A' and int(t[1:]) < d)]
    ok = bad = 0
    for L in range(1, max_tokens + 1):
        for X in itertools.product(allowed, repeat=L):
            if X[0] == 'D' or (d and X[-1] == 'A%d' % d):
                continue
            x = sum((TOK[t] for t in X), ())
            t = A(d) + x
            for n in (1, 2, 3):
                ref = tuple(harness.fs(t, n))
                for z in PREFIXES:
                    if tuple(harness.fs(z + t, n)) == z + ref:
                        ok += 1
                    else:
                        bad += 1
                        print('RAW_BAD', d, X, z, n, flush=True)
    return ok, bad


def add_check():
    runner.setup(0)
    S.load_cache(runner.TAIL_CACHE)
    vals = {(t, d): v[1] for (b, flag, t, d), v in S._F_CACHE.items()
            if b == S.BASE and not flag and v[0] == 'value'}
    ok = bad = 0
    for (t, d), v in vals.items():
        tk = S.tokens(t)
        for i, x in enumerate(tk[:-1]):
            if x != 'A0':
                continue
            z, r = S.seq(tk[:i+1]), S.seq(tk[i+1:])
            if (z, d) in vals and (r, d) in vals:
                if cmp(add(vals[(z, d)], vals[(r, d)]), v) == 0:
                    ok += 1
                else:
                    bad += 1
                    print('ADD_BAD', tk, d, i, flush=True)
    return len(vals), ok, bad


if __name__ == '__main__':
    for d, m in ((0, 5), (1, 4), (2, 4)):
        print('raw d=%d tokens<=%d ok %d bad %d' % ((d, m) + raw_check(d, m)), flush=True)
    print('ADD values %d ok %d bad %d' % add_check(), flush=True)
