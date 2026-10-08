"""Single lex-order pass for ./ssosn --fix: every fs(S,n) is lex-smaller than S,
so values of expansions are already known when S is reached.
usage: python3 fixtable.py TOP MAXLEN OUT.json"""
import sys, json
import evalord as E
from ordinal import ZERO, succ, lt, show
ns = {}; exec(compile(open('ssosn').read(), 'ssosn', 'exec'), ns)
Seq = ns['Seq']
def fs(S, n):
    c = Seq(S, 'new').cut()
    return tuple(S[:c]) + (tuple(S[c:-1]) + (S[-1] - 1,)) * n
NS = (1, 2, 3)
top = tuple(int(x) for x in sys.argv[1].split(',')); ml = int(sys.argv[2])
seen = set(); st = [top]
while st:
    S = st.pop()
    if S in seen or len(S) > ml: continue
    seen.add(S)
    if not S: continue
    if S[-1] == 0: st.append(S[:-1]); continue
    for n in NS: st.append(fs(S, n))
Ss = sorted(seen); val = {}
for S in Ss:
    if not S: val[S] = ZERO
    elif S[-1] == 0:
        if S[:-1] in val: val[S] = succ(val[S[:-1]])
    else:
        xs = [val.get(fs(S, n)) for n in NS]
        if all(x is not None for x in xs):
            r = E.sup(xs)
            if r is not None: val[S] = r
ks = [S for S in Ss if S in val]
viol = sum(1 for a, b in zip(ks, ks[1:]) if not lt(val[a], val[b]))
lim = [S for S in Ss if S and S[-1] != 0]
print(len(Ss), 'std;', len(lim), 'limit;', sum(S in val for S in lim), 'valued; order violations', viol)
json.dump([[list(S), show(val[S]) if S in val else None] for S in lim], open(sys.argv[3], 'w'))
