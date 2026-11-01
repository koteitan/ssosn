"""§43 conjecture: rank of a W/D/V copy word through 0/1/2 "bits" (not proved).

bits: W -> 0, D -> 1, V -> replace a final 1 by 2 (else append 2).
  This encodes the real law X V[n] = X D^n 0: the D^n tail is 1^n, whose sup is 2.
v2 = conj2.v on the bits, with a hook for self-referential blocks:
  a block u whose every run starts with 2 has value e_(v2(T2(u))),
  T2(u) = drop the first entry (a 2) of every run.
  So 2 = e0, 202 = e1, 21 = e_w, 22 = e_e0, 2102 = e_(w+1).
Other self-referential blocks raise ValueError.
For 0/1 words this is the binary rank used by token_tree.copy_rank.
"""
import sys
from pathlib import Path
sys.path[:0] = [str(Path(__file__).resolve().parent), str(Path(__file__).resolve().parent.parent)]
import conj2
from ordinal import ZERO, ONE, P, add, w


def bits(copies):
    out = []
    for t in copies:
        if t == 'W':
            out.append(0)
        elif t == 'D':
            out.append(1)
        elif t == 'V':
            if out and out[-1] == 1:
                out[-1] = 2
            else:
                out.append(2)
        else:
            raise ValueError(('bits: token', t))
    return tuple(out)


def T2(u):
    runs, cur = [], []
    for x in u:
        if x == 0:
            runs.append(cur); cur = []
        else:
            cur.append(x)
    runs.append(cur)
    if not all(r and r[0] == 2 for r in runs):
        raise ValueError(('T2: run not led by 2', u))
    out = []
    for k, r in enumerate(runs):
        if k:
            out.append(0)
        out += r[1:]
    return tuple(out)


def v2(y):
    r = ZERO
    for u in conj2.units(y):
        if u == (0,):
            r = add(r, ONE); continue
        if u == (2,):
            r = add(r, P(ONE, ZERO)); continue
        t = conj2.T(u)
        if t == u:
            r = add(r, P(ONE, v2(T2(u)))); continue
        r = add(r, w(add(ONE, v2(t))))
    return r


def rank(copies):
    return v2(bits(copies))


if __name__ == '__main__':
    from ordinal import show
    for word in sys.argv[1:]:
        c = tuple(word)
        print(word, bits(c), show(rank(c)))
