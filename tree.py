"""Tree form of the (0,0)-fragment: a term is a tuple of units; a unit is 'z' (a 0)
or ('b', u) (a block whose T is u).  flat/parse convert to 0/1 sequences."""
import conj
def parse(Y):
    out = []
    for s in conj.units(Y):
        out.append('z' if s == '0' else ('b', parse(conj.T(s))))
    return tuple(out)
def flat(t):
    s = ''
    for u in t:
        if u == 'z': s += '0'
        else:
            inner = flat(u[1]); s += '0'.join('1' * (len(r) + 1) for r in inner.split('0'))
    return s
def H(u, k):
    if not u: return ('z',) * k
    if u[-1] == 'z': return (('b', u[:-1]), 'z', 'z') * k
    Pu, w = u[:-1], u[-1][1]
    h = H(w, k); assert h[-1] == 'z'
    return (('b', Pu + h[:-1]), 'z')
def E(t, k):
    assert t[-1] != 'z'
    return t[:-1] + H(t[-1][1], k)
