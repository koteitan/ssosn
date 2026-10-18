"""Where is the real cut c = mbp(p(br)) of a standard token string after (0,0,2,1)?
Classify by the last token and by the token boundary at which the cut lies (2026-10-18).
usage (from the repository root): python3 work/cutclass.py N"""
import sys, os
_h = os.path.dirname(os.path.abspath(__file__)); sys.path[:0] = [_h, os.path.dirname(_h)]
import harness, std
from collections import Counter, defaultdict
def A(k): return (0,1,2) + (0,2) * k
TOKS = {'A0': A(0), 'A1': A(1), 'A2': A(2), 'E1': A(1) + (1,), 'W': A(0) + (1,)}
HI = (0,0,2,1,0,2)
def seq(t): return (0,0,2,1) + sum((TOKS[x] for x in t), ())
def cutpos(t):
    """cut as (number of whole tokens before it, offset inside the next token); 'G=00' if cut = 2"""
    S = seq(t); c = harness.Seq(S, 'new').cut()
    if c == 2: return 'G=00'
    if c == 3: return 'G=002'
    pos = 4; i = 0
    while i < len(t) and pos + len(TOKS[t[i]]) <= c: pos += len(TOKS[t[i]]); i += 1
    return 'after %d tok' % i if pos == c else 'inside tok %d (+%d)' % (i, c - pos)
stats = defaultdict(Counter); ex = {}
frontier = [()]
for d in range(int(sys.argv[1])):
    new = []
    for t in frontier:
        for k in TOKS:
            u = t + (k,); S = seq(u)
            if S >= HI or not std.is_standard(S): continue
            new.append(u)
            cp = cutpos(u)
            # describe the cut relative to the end: how many tokens from the end
            if cp.startswith('after'):
                i = int(cp.split()[1]); cp = 'after tok, %d from end' % (len(u) - i)
            key = u[-1]
            stats[key][cp] += 1; ex.setdefault((key, cp), ' '.join(u))
    frontier = new
for key in sorted(stats):
    print(key, dict(stats[key]))
for (key, cp), e in sorted(ex.items()): print('  ex', key, cp.ljust(28), e)
