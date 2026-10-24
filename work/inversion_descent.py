"""Locate the root of a value inversion by descending through real terms (2026-10-24, Claude).

Given standard a <lex b with V(a) >= V(b): no gaps gives a least n with b[n] >=lex a, and
V(b[n]) < V(b) <= V(a) must hold, so (a, b[n]) is again an inversion. Repeat. The descent ends
at a word b* whose real term b*[n] has V(b*[n]) >= V(b*) (term not below the parent), at a
successor b* with V(b*) != V(b*[:-1])+1, or when b*[n] == a (then V(a) >= V(b*) > V(a) fails,
i.e. b*[n] is not below b*). V = token_tree.value with the flags given by CAND
(general | cut | seed).
usage: CAND=seed python3 work/inversion_descent.py "D D D A0 W D D W A2" "D D D A1"
"""
import os, sys
sys.path[:0] = [os.path.dirname(os.path.abspath(__file__)), os.path.dirname(os.path.dirname(os.path.abspath(__file__)))]
import harness, token_tree as T
from ordinal import cmp, show
c = os.environ.get('CAND', 'seed')
if c in ('cut', 'seed'): T.CUT_COPY_ACTION_EXPERIMENT = True
if c == 'seed': T.CONSISTENT_COPY_SEED_EXPERIMENT = True
if c == 'general': T.GENERAL_COPY_EXPERIMENT = True
R = {'A0': (0,1,2), 'A1': (0,1,2,0,2), 'A2': (0,1,2,0,2,0,2), 'A3': (0,1,2,0,2,0,2,0,2),
     'W': (0,1,2,1), 'E1': (0,1,2,0,2,1), 'D': (0,2)}
def seq(ts): return (0,0,2,1) + sum((R[t] for t in ts.split()), ())
def tok(s):
    s = tuple(s[4:]); out = []; i = 0
    while i < len(s):
        if s[i:i+3] == (0,1,2):
            j = i+3; k = 0
            while s[j:j+2] == (0,2): j += 2; k += 1
            if s[j:j+1] == (1,) and k <= 1: out.append('W' if k == 0 else 'E1'); j += 1
            else: out.append('A%d' % k)
            i = j
        elif s[i:i+2] == (0,2): out.append('D'); i += 2
        else: out.append(''.join(map(str, s[i:]))); break
    return ' '.join(out)
def V(s): return T.value(tuple(s))
def descend(a, b, cap=400):
    va = V(a)
    for step in range(200):
        vb = V(b)
        print('%3d  b = %-60s V(b) = %s' % (step, tok(b), show(vb)), flush=True)
        if b[-1] == 0:
            vp = V(b[:-1])
            if cmp(vb, vp) <= 0: print('ROOT: successor', tok(b)); return
            b = b[:-1]; continue
        for n in range(1, cap):
            t = tuple(harness.fs(b, n))
            if t >= a: break
        else:
            print('no term >= a within cap'); return
        vt = V(t)
        if t == a or cmp(vt, vb) >= 0:
            print('ROOT: term n=%d of b is not below b' % n)
            print('   b    =', tok(b), show(vb))
            print('   b[n] =', tok(t), show(vt))
            return
        b = t
    print('step limit')
a = seq(sys.argv[1]); b = seq(sys.argv[2])
print('a =', sys.argv[1], show(V(a)))
assert a < b and cmp(V(a), V(b)) >= 0, 'not an inversion'
descend(a, b)
