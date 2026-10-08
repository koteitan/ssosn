"""Plain-definition ordinals (NS=1..3) for every standard sequence below TOP
(closure under fs n<=3, length<=MAXLEN), BUDGET seconds each.
Writes rows 'S<TAB>blocks<TAB>ordinal' to OUT in lex order."""
import sys, signal
import evalord as E, blocks as K
from explore import closure
E.NS = (1, 2, 3)
top = tuple(int(x) for x in sys.argv[1].split(","))
maxlen, budget, out = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
Ss = sorted(S for S in closure([top], nmax=3, maxlen=maxlen) if S and S[-1] != 0)
def alarm(*a): raise TimeoutError
signal.signal(signal.SIGALRM, alarm)
with open(out, "w") as f:
    for S in Ss:
        signal.alarm(budget)
        try:
            v = E.show(E.o(S))
        except TimeoutError:
            v = "?"
        signal.alarm(0)
        b = K.blocks(S) if K.is01(S) else ""
        f.write(f"({','.join(map(str,S))})\t{b}\t{v}\n"); f.flush()
print(len(Ss), "rows")
