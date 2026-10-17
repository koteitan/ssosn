"""Value S by the sup of its real terms; every term is valued after all of its prefixes, so that
the clean-value memo of rule6 warms up (2026-10-17).
usage (from the repository root): python3 work/warm.py MAXD N SEQ ...   (SEQ like 002101210121, N terms)"""
import sys, os, signal
_here = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [_here, os.path.dirname(_here)]
import rule6, std, lift, harness, util
import evalord as E
from ordinal import show
lift.unlift((2,1))
rule6.USE_LIFT = True; rule6.EXT = True; rule6.MORE = True; rule6.MAXD = int(sys.argv[1])
class TO(Exception): pass
def al(*a): raise TO
signal.signal(signal.SIGALRM, al)
def val(S, tl=120):
    signal.alarm(tl)
    try:
        rule6.st['taint'] = 0; rule6.st['depth'] = 0
        r = rule6.R(S); return r, rule6.st['taint'] > 0
    except TO:
        rule6.st['depth'] = 0; return 'TIMEOUT', None
    finally: signal.alarm(0)
def warm(S):
    for i in range(3, len(S) + 1):
        if S[i-1] != 0: val(S[:i])
    return val(S)
N = int(sys.argv[2])
for s in sys.argv[3:]:
    S = tuple(int(c) for c in s)
    xs = []; clean = True
    for n in range(1, N + 1):
        T = harness.fs(S, n); r, tn = warm(T)
        print('  ', n, util.t2s(T).ljust(60), show(r) if r not in (None, 'TIMEOUT') else r, 'TAINT' if tn else '', flush=True)
        xs.append(r); clean &= (tn is False)
    ok_xs = all(x not in (None, 'TIMEOUT') for x in xs)
    s_ = E.sup(xs) if ok_xs else None
    ok = s_ is not None and E.check(s_, xs, 3)
    s3 = rule6.sup3(xs) if ok_xs else None
    print(s, 'std' if std.is_standard(S) else 'NONSTD', 'sup', show(s_) if s_ else None, 'ok' if ok else 'nocheck', 'sup3', show(s3) if s3 else None, 'CLEAN' if clean else 'TAINT', flush=True)
