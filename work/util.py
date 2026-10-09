import harness
from ordinal import show
def s2t(s): return tuple(int(c) for c in s.replace(',', ''))
def t2s(t): return ''.join(map(str, t))
def exp(R, s, NS=(1, 2, 3, 4)):
    S = s2t(s) if isinstance(s, str) else s
    r = R(S)
    print(t2s(S), '=', r and show(r))
    for n in NS:
        T = harness.fs(S, n); x = R(T)
        print('   [%d]' % n, t2s(T).ljust(40), x and show(x))
