"""Single pass over standard sequences in lex order.

Every expansion fs(S, n) is lex-smaller than S, and S⌢0 comes right after S,
so processing the enumerated standard sequences in ascending lex order finds
every needed value already in the table: no recursion, no blow-up.

usage: python3 table.py TOP MAXLEN [SHOWLEN]
"""
import sys
import ssos
from explore import closure
from ordinal import ZERO, succ, lt, show
from evalord import sup

NS = (1, 2, 3)


def build(top, maxlen):
    Ss = sorted(closure([top], nmax=max(NS), maxlen=maxlen))
    val = {}
    unknown = []
    for S in Ss:
        if not S:
            val[S] = ZERO
        elif S[-1] == 0:
            if S[:-1] in val:
                val[S] = succ(val[S[:-1]])
        else:
            xs = [val.get(ssos.fs(S, n)) for n in NS]
            xs = [x for x in xs if x is not None]
            r = sup(xs) if len(xs) == len(NS) else None
            if r is None:
                unknown.append(S)
            else:
                val[S] = r
    return Ss, val, unknown


def monotone_errors(Ss, val):
    ks = [S for S in Ss if S in val]
    return [(a, b) for a, b in zip(ks, ks[1:]) if not lt(val[a], val[b])]


if __name__ == "__main__":
    top = tuple(int(x) for x in sys.argv[1].split(","))
    Ss, val, unk = build(top, int(sys.argv[2]))
    errs = monotone_errors(Ss, val)
    print(f"{len(Ss)} standard seqs, {len(val)} valued, {len(unk)} unknown, "
          f"{len(errs)} lex/ordinal order violations")
    for a, b in errs[:5]:
        print("  VIOLATION", a, show(val[a]), ">=", b, show(val[b]))
    if len(sys.argv) > 3:
        sl = int(sys.argv[3])
        for S in Ss:
            if S and S[-1] != 0 and len(S) <= sl:
                print(S, show(val[S]) if S in val else "?")
