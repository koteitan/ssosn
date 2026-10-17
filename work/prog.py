"""Evaluate token strings after (2,1) progressively (every token prefix, in order) so that the
clean-value memo of rule6 warms up (2026-10-17).
usage (from the repository root): python3 work/prog.py MAXD "A0 1 A1 1" "A0 1 A0 1" ..."""
import sys, os, signal
_here = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [_here, os.path.dirname(_here)]
import rule6, std, lift, harness, util
from ordinal import show
lift.unlift((2,1))
rule6.USE_LIFT = True; rule6.EXT = True; rule6.MORE = True; rule6.MAXD = int(sys.argv[1])
TOK = {'A0': (0,1,2), 'A1': (0,1,2,0,2), 'A2': (0,1,2,0,2,0,2), 'A3': (0,1,2,0,2,0,2,0,2), '1': (1,)}
class TO(Exception): pass
def al(*a): raise TO
signal.signal(signal.SIGALRM, al)
def val(S, tl=60):
    signal.alarm(tl)
    try:
        rule6.st['taint'] = 0; rule6.st['depth'] = 0
        r = rule6.R(S); return (show(r) if r is not None else None), rule6.st['taint'] > 0
    except TO:
        rule6.st['depth'] = 0; return 'TIMEOUT', None
    finally: signal.alarm(0)
done = set()
for c in sys.argv[2:]:
    toks = c.split(); v = (2,1)
    for i, t in enumerate(toks):
        v += TOK[t]
        if v in done: continue
        done.add(v); S = (0,0) + v
        r, tn = val(S)
        if i == len(toks) - 1 or tn:
            print(' '.join(toks[:i+1]).ljust(30), util.t2s(S).ljust(44), 'std' if std.is_standard(S) else 'NONSTD', r, 'TAINT' if tn else '', flush=True)
