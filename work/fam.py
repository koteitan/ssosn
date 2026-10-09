import sys, harness, rule3, util
import evalord as E
from ordinal import show
Ss = harness.closure([util.s2t('002102012101202102')], maxlen=21)
rule3.iterate(Ss, rounds=200, log=False)
def val(S):
    """rule3 value; if it fails the sup test, the sup of its terms (one level)."""
    r = rule3.R(S)
    if S[-1] == 0 or not rule3.single_selfref(S): return r, ''
    xs = [rule3.R(harness.fs(S, n)) for n in (1, 2, 3, 4, 5)]
    if any(x is None for x in xs): return r, '?terms'
    if r is not None and E.check(r, xs, 3): return r, ''
    return E.sup(xs), '(fixed; rule3 said %s)' % (r and show(r))
for s in sys.argv[1:]:
    S = util.s2t(s); r, note = val(S)
    print(s.ljust(28), r and show(r), note)
