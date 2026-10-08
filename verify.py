"""Check the rule-based ordinal assignment fast.o on all standard sequences
below TOP (closure under fs with n<=3, length <= MAXLEN):

  (a) lex order of standard sequences == ordinal order
  (b) every limit S: o(S) is the guessed sup of o(fs(S,n)), n = 1..3,
      and passes check(): o(fs(S,n)) < o(S) and o(S)[k] <= o(fs(S,3))

usage: python3 verify.py TOP MAXLEN [SHOWLEN]
"""
import sys
import ssos
import fast
from explore import closure
from ordinal import lt, show
from evalord import sup, check

top = tuple(int(x) for x in sys.argv[1].split(","))
Ss = sorted(closure([top], nmax=3, maxlen=int(sys.argv[2])))
val = {S: fast.o(S) for S in Ss}
bad_order = [(a, b) for a, b in zip(Ss, Ss[1:]) if not lt(val[a], val[b])]
bad_sup = []
for S in Ss:
    if S and S[-1] != 0:
        xs = [fast.o(ssos.fs(S, n)) for n in (1, 2, 3)]
        if not check(val[S], xs, 2) or sup(xs) != val[S]:
            bad_sup.append((S, [show(x) for x in xs], show(val[S])))
print(f"{len(Ss)} standard seqs; order violations {len(bad_order)}; "
      f"sup mismatches {len(bad_sup)}")
for a, b in bad_order[:5]:
    print("  ORDER", a, show(val[a]), ">=", b, show(val[b]))
for x in bad_sup[:5]:
    print("  SUP", *x)
if len(sys.argv) > 3:
    for S in Ss:
        if S and S[-1] != 0 and len(S) <= int(sys.argv[3]):
            print(S, show(val[S]))
