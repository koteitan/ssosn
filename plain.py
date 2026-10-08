"""Plain-definition ordinals (no shortcut rules) for standard sequences
below TOP, each with a time budget; prints lex-sorted limit sequences."""
import sys, signal
import evalord as E
from explore import closure
E.NS = (1, 2, 3)
top = tuple(int(x) for x in sys.argv[1].split(","))
Ss = sorted(S for S in closure([top], nmax=3, maxlen=int(sys.argv[2])) if S and S[-1] != 0)
budget = int(sys.argv[3])
def alarm(*a): raise TimeoutError
signal.signal(signal.SIGALRM, alarm)
for S in Ss:
    signal.alarm(budget)
    try:
        v = E.show(E.o(S))
    except TimeoutError:
        v = "(timeout)"
    except E.Unknown as e:
        v = "(no sup: %s)" % (e.args[0][1],)
    signal.alarm(0)
    print(S, v, flush=True)
