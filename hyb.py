"""Hybrid evaluator for ./ssosn --fix: plain recursion (guessed sup over n=1..3),
but sequences of the (0,0)-fragment (entries <= 1) are valued by conj.o."""
import sys, signal, time
import evalord as E, conj, conj2
from ordinal import show, succ
ns = {}; exec(compile(open('ssosn').read(), 'ssosn', 'exec'), ns)
Seq = ns['Seq']
def fs(S, n):
    c = Seq(S, 'new').cut()
    return tuple(S[:c]) + (tuple(S[c:-1]) + (S[-1] - 1,)) * n
E.ssos.fs = fs
NS = (1, 2, 3)
memo = {}
def _hook(u):
    x = o((0, 0) + tuple(u))       # value of the block alone: o((0,0) ⌢ u) = 2 + value
    return x
conj2.HOOK = _hook
SPLIT = True
USE2 = True
from ordinal import add
def split_at(S):
    """last j >= 2 with S[j] = S[j+1] = 0 such that the cut of S is >= j
    (the expansion does not reach into S[:j]); None if there is none."""
    c = Seq(S, 'new').cut()
    for j in range(len(S) - 2, 1, -1):
        if S[j] == 0 and S[j + 1] == 0 and c >= j:
            return j
    return None
def o(S):
    S = tuple(S)
    if S in memo: return memo[S]
    if len(S) >= 2 and S[:2] == (0, 0) and max(S) <= 1:
        r = conj.o(S)
    elif USE2 and (c2 := conj2.o(S)) is not None:
        r = c2
    elif not S: r = ()
    elif S[-1] == 0: r = succ(o(S[:-1]))
    elif SPLIT and (j := split_at(S)) is not None:
        r = add(o(S[:j]), o(S[j:]))
    else:
        xs = [o(fs(S, n)) for n in NS]
        r = E.sup(xs)
        if r is None: raise E.Unknown((S, [show(x) for x in xs]))
    memo[S] = r
    return r
if __name__ == '__main__':
    def alarm(*a): raise TimeoutError
    signal.signal(signal.SIGALRM, alarm)
    B = int(sys.argv[1])
    for arg in sys.argv[2:]:
        S = tuple(int(x) for x in arg.split(','))
        t = time.time(); signal.alarm(B)
        try: v = show(o(S))
        except TimeoutError: v = '(timeout)'
        except E.Unknown as e: v = '(no sup: %s)' % (e.args[0][1],)
        signal.alarm(0)
        print(''.join(map(str, S)).ljust(16), v, '%.1fs' % (time.time() - t), 'memo', len(memo), flush=True)
