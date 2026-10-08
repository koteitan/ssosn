"""Profile the plain recursion of hyb.o (self-referential blocks valued by recursion).
usage: python3 debug_prof.py 0,0,2,1,0,2 20     (sequence, seconds)
prints: calls, memo size, max recursion depth, new sequences by length, deepest call chain."""
import sys, signal, time, collections
import hyb, conj2, lower
conj2.HOOK = lower.fallback          # pure recursion for self-ref blocks
orig = hyb.o
depth = [0]; maxd = [0]; calls = [0]
lens = collections.Counter(); path = []; deepest = []
kind = collections.Counter()
def o(S):
    S = tuple(S); calls[0] += 1
    if S in hyb.memo: kind['memo-hit'] += 1; return hyb.memo[S]
    lens[len(S)] += 1
    depth[0] += 1; path.append(S)
    if depth[0] > maxd[0]: maxd[0] = depth[0]; deepest[:] = list(path)
    try: return orig(S)
    finally: depth[0] -= 1; path.pop()
hyb.o = o
def alarm(*a): raise TimeoutError
signal.signal(signal.SIGALRM, alarm); signal.alarm(int(sys.argv[2]))
S = tuple(int(x) for x in sys.argv[1].split(','))
t = time.time()
try: print('value', hyb.show(o(S)))
except TimeoutError: print('timeout')
print('time %.1f calls %d memo %d maxdepth %d' % (time.time()-t, calls[0], len(hyb.memo), maxd[0]))
print('new seqs by length:', sorted(lens.items()))
print('deepest chain (len, seq):')
for s in deepest[:60]: print(' ', len(s), ''.join(map(str, s)))
