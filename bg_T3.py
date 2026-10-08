import signal, sys, time
import evalord as E
E.NS = (1, 2, 3)
best = [None]
orig = E.sup
def sup(xs):
    r = orig(xs)
    if r is not None and (best[0] is None or E.lt(best[0], r)):
        best[0] = r
    return r
E.sup = sup
def report(*a):
    print(time.strftime("%H:%M:%S"), "memo", len(E.memo), "largest sup so far:", E.show(best[0]), flush=True)
    signal.alarm(30)
signal.signal(signal.SIGALRM, report); signal.alarm(30)
S = (0,0,1,0,1,0,0,1,0,1,0,0,1,0,1)
print("T3 =", E.show(E.o(S)), flush=True)
