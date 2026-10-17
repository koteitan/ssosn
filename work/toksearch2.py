"""Token search above e0*2 (2026-10-17): append tokens A0, A1, A2, 1 to (2,1), keep standard
forms below (0,0,2,1,0,2), value them with rule6 (USE_LIFT, EXT, MORE), 5 s per value.
usage (from the repository root): timeout 1500 python3 work/toksearch2.py [OUT.pkl]"""
import sys, os, time, pickle, signal, functools
_here = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [_here, os.path.dirname(_here)]
import harness, rule6, util, std, lift
from ordinal import show, cmp
lift.unlift((2, 1))
rule6.USE_LIFT = True; rule6.EXT = True; rule6.MAXD = 6; rule6.MORE = True
rule6.EXT121 = rule6.EXT121E = rule6.NOREGION = rule6.RELLIFT = False
TOK = {'A0': (0,1,2), 'A1': (0,1,2,0,2), 'A2': (0,1,2,0,2,0,2), '1': (1,)}
LO, HI = (0,0,2,1,0,1,2,0,2,1), (0,0,2,1,0,2)
class TO(Exception): pass
def alarm(*a): raise TO
signal.signal(signal.SIGALRM, alarm)
t0 = time.time(); frontier = [((), (2,1))]; table = {}; seen = set(); nto = 0
for depth in range(9):
    new = []
    for toks, u in frontier:
        for k, tk in TOK.items():
            if k == '1' and toks and toks[-1] == '1': continue
            v = u + tk; S = (0,0) + v
            if v in seen or S >= HI: continue
            seen.add(v)
            if not std.is_standard(S): continue
            new.append((toks + (k,), v))
            if S < LO: continue
            signal.alarm(5)
            try:
                r, tn = rule6.value(S)
            except TO:
                nto += 1; rule6.st['depth'] = 0; continue
            finally:
                signal.alarm(0)
            if tn or r is None: continue
            if r not in table or len(v) < len(table[r][1]): table[r] = (toks + (k,), v)
    frontier = new
    print('depth', depth+1, 'standard', len(new), 'clean values', len(table), 'timeouts', nto,
          '%.0fs' % (time.time()-t0), flush=True)
    if time.time() - t0 > 900: break
pickle.dump(table, open(sys.argv[1] if len(sys.argv) > 1 else 'toktable2.pkl', 'wb'))
rows = sorted(table.items(), key=functools.cmp_to_key(lambda a, b: cmp(a[0], b[0])))
for r, (toks, v) in rows:
    print(show(r).ljust(34), ' '.join(toks).ljust(34), util.t2s(v), flush=True)
