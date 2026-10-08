"""Ordinals of standard sequences for ./ssosn --fix (plain recursion, guessed sup).
usage: python3 fixeval.py TOP MAXLEN BUDGET OUT.json"""
import sys, json, signal
import evalord as E
ns = {}; exec(compile(open('ssosn').read(), 'ssosn', 'exec'), ns)
Seq = ns['Seq']
def fs(S, n):
    c = Seq(S, 'new').cut()
    return tuple(S[:c]) + (tuple(S[c:-1]) + (S[-1] - 1,)) * n
E.ssos.fs = fs
E.NS = (1, 2, 3)
def closure(top, maxlen):
    seen = set(); st = [top]
    while st:
        S = st.pop()
        if S in seen or len(S) > maxlen: continue
        seen.add(S)
        if not S: continue
        if S[-1] == 0: st.append(S[:-1]); continue
        for n in (1, 2, 3): st.append(fs(S, n))
    return seen
top = tuple(int(x) for x in sys.argv[1].split(','))
Ss = sorted(S for S in closure(top, int(sys.argv[2])) if S and S[-1] != 0)
def alarm(*a): raise TimeoutError
signal.signal(signal.SIGALRM, alarm)
out = []
for S in Ss:
    signal.alarm(int(sys.argv[3]))
    try: v = E.show(E.o(S))
    except TimeoutError: v = None
    except E.Unknown: v = '?'
    signal.alarm(0)
    out.append([list(S), v])
json.dump(out, open(sys.argv[4], 'w'))
vals = [(S, E.o(tuple(S))) for S, v in out if v not in (None, '?')]
viol = sum(1 for (a, x), (b, y) in zip(vals, vals[1:]) if not E.lt(x, y))
print(len(Ss), 'limit std;', len(vals), 'valued;', sum(v is None for _, v in out), 'timeout;', sum(v == '?' for _, v in out), 'no sup; order violations', viol)
