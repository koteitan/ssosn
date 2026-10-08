"""Count how hyb.o resolves each new sequence (fragment / conj2 / succ / split / sup)
and where the cut falls, for 10 s of the plain recursion on (0,0,2,1,0,2).
usage: python3 debug_kind.py"""
import sys, signal, time, collections, os
import hyb, conj, conj2, lower
conj2.HOOK = lower.fallback
kind = collections.Counter(); cutpos = collections.Counter(); grow = []
orig_fs = hyb.fs
def fs(S, n):
    T = orig_fs(S, n); c = hyb.Seq(S, 'new').cut()
    cutpos['cut=2 (copy all)' if c == 2 else 'cut>2'] += 1
    grow.append(len(T) - len(S)); return T
hyb.fs = fs
orig = hyb.o
def o(S):
    S = tuple(S)
    if S in hyb.memo: return hyb.memo[S]
    if len(S) >= 2 and S[:2] == (0,0) and max(S) <= 1: k = 'fragment'
    elif conj2.o(S) is not None: k = 'conj2'
    elif S[-1] == 0: k = 'succ'
    elif hyb.split_at(S) is not None: k = 'split'
    else: k = 'sup S[1..3]'
    kind[k] += 1
    return orig(S)
hyb.o = o
def alarm(*a): raise TimeoutError
signal.signal(signal.SIGALRM, alarm); signal.alarm(10)
marks = []
t0 = time.time()
try: o((0,0,2,1,0,2))
except TimeoutError: pass
print('kinds:', dict(kind)); print('cuts:', dict(cutpos))
print('length change per expansion: avg %.1f, max %d' % (sum(grow)/len(grow), max(grow)))
