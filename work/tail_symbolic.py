"""Symbolic tail values F after a unit (2026-10-25, Claude). Experimental, hypothesis S.

For a tail T after the base X⌢A0, the contracted real terms have the form T[n] = H Q^(n-1) V.
- T ends with A0:            F(T) = F(T minus A0) + 1.
- Q = A1 R, R without A0 (hypothesis S): each block adds 1+F(R) at depth 1, so
                             F(T) = bump_last(F(H), 1, (1+F(R))·ω).
- other Q:                   F(T) = sup of F(T[1..3]) (evalord.sup, checked with T[4]).
Only H and R (shorter) or T[n] are consulted. Values are relative to the base.
usage: python3 work/tail_symbolic.py "D D D A0" "W D D" "W D W D" ...
"""
import os, sys
from functools import lru_cache
sys.path[:0] = [os.path.dirname(os.path.abspath(__file__)), os.path.dirname(os.path.dirname(os.path.abspath(__file__)))]
import harness, evalord
import token_value as TV
from ordinal import ZERO, ONE, OMEGA, P, add, cmp, fs, is_limit, show
sys.setrecursionlimit(100000)
R = {'A0': (0,1,2), 'A1': (0,1,2,0,2), 'A2': (0,1,2,0,2,0,2), 'W': (0,1,2,1), 'D': (0,2)}
A0, A1 = (0,1,2), (0,1,2,0,2)
BASE = None


class Undecided(Exception):
    pass


def mul_omega(x):
    """x·ω for x > 0: ω^(e+1) where ω^e is the leading term."""
    lead = x[0]
    return TV.w(add(lead[2] if lead[1] == ZERO else (lead,), ONE)) if lead[1] == ZERO else TV.w(add((lead,), ONE))


def _shift_names(names, delta):
    out=[]
    for name in names:
        if name.startswith('A'):
            k=int(name[1:])+delta
            if k<0:raise Undecided('tail leaves opened depth')
            out.append('A%d'%k)
        else:out.append(name)
    return tuple(out)


def _base_at_depth(depth):
    if depth==0:return BASE
    # BASE ends in the reference unit A0. Replace that unit by A_depth so
    # its actual expansions open terms at the same depth as the caller.
    if BASE[-3:]!=A0:raise Undecided('reference base does not end in A0')
    return BASE[:-3]+seq(('A%d'%depth,))


def induced(t, n, depth=0):
    actual_base=_base_at_depth(depth)
    actual_tail=seq(_shift_names(tokens(t),depth))
    src = actual_base + actual_tail
    c = tuple(harness.fs(src, n))
    term = (0,) if src[-1] == 1 else (0, 1) if src[-1] == 2 else None
    if term is None or c[-len(term):] != term:
        raise Undecided('terminal')
    core = c[:-len(term)]
    if core[:len(actual_base)] != actual_base:
        raise Undecided('escapes unit')
    raw_tail=core[len(actual_base):]
    # At positive opened depth, the closing A0 0 belongs to the generated
    # real term's outer successor. It is outside the relative tail; remove
    # that final A0 before translating the remaining A_j down by depth.
    if depth and raw_tail[-3:]==A0:
        raw_tail=raw_tail[:-3]
    actual_tokens=tokens(raw_tail)
    if actual_tokens is None:raise Undecided('unrecognized induced tail')
    normalized=_shift_names(actual_tokens,-depth)
    return seq(normalized)


def periodic(t, depth=0):
    c1, c2, c3 = induced(t, 1,depth), induced(t, 2,depth), induced(t, 3,depth)
    q = len(c2) - len(c1)
    if q <= 0 or len(c3) - len(c2) != q:
        raise Undecided('not periodic')
    splits = []
    for i in range(len(c1), -1, -1):
        Q = c2[i:i+q]
        if c2 == c1[:i] + Q + c1[i:] and c3 == c1[:i] + Q + Q + c1[i:]:
            splits.append((c1[:i], Q, c1[i:], (c1, c2, c3)))
    if not splits:
        raise Undecided('no H Q V split')
    # A0 D and A1 are the same raw word; prefer the split whose block is A1 R with R free of A0
    # (an A0 inside R returns to depth 0, so the block does not stay at depth 1).
    for sp in splits:
        if s_block(sp[1]):
            return sp
    return splits[0]


def tokens(s):
    out = []; i = 0
    while i < len(s):
        if s[i:i+3] == (0, 1, 2):
            j = i + 3; k = 0
            while s[j:j+2] == (0, 2):
                j += 2; k += 1
            if s[j:j+1] == (1,) and k == 0:
                out.append('W'); j += 1
            else:
                out.append('A%d' % k)
            i = j
        elif s[i:i+2] == (0, 2):
            out.append('D'); i += 2
        else:
            return None
    return out


def s_block(Q):
    if Q[:5] != A1 or Q[5:7] == (0, 2):
        return False
    r = tokens(Q[5:])
    return r is not None and 'A0' not in r


def epsilon_index(x):
    """Return a when x is the single principal epsilon ordinal ε_a."""
    if len(x)==1 and x[0][1]==ONE:
        return x[0][2]
    return None


def checked_limit(a, xs, K=None):
    if not is_limit(a) or not all(cmp(x,a)<0 for x in xs):
        return False
    if K is None:K=len(xs)-1
    return all(cmp(fs(a,k),xs[-1])<=0 for k in range(1,K+1))


def fixedpoint_sup(xs):
    """Sup candidate with ε-index and next-fixed-point cases, checked by FS."""
    if not xs or any(cmp(a,b)>=0 for a,b in zip(xs,xs[1:])):
        return None
    candidates=[]
    direct=evalord.sup(xs)
    if direct is not None:candidates.append(direct)
    indices=[epsilon_index(x) for x in xs]
    if all(a is not None for a in indices):
        index_sup=evalord.sup(indices)
        if index_sup is not None:candidates.append(P(ONE,index_sup))
    try:
        candidates.append(evalord.next_fp(ONE,xs[-1]))
    except Exception:
        pass
    candidates.sort(key=evalord._Key)
    for a in candidates:
        # A fixed number of fundamental-sequence checks rejects short
        # finite-tower guesses such as ω^ω^ω^ω^ω² when the samples approach ε0.
        if checked_limit(a,xs,K=max(4,len(xs)-1)):return a
    return None


@lru_cache(maxsize=None)
def F(t, depth=0):
    if not t:
        return ZERO
    if t[-3:] == A0:
        return add(F(t[:-3],depth), ONE)
    H, Q, V, cs = periodic(t,depth)
    if s_block(Q):
        r = Q[5:]
        step = add(ONE, F(r,depth))
        amount = mul_omega(step)
        return TV.bump_last(F(H,depth), 1, amount)
    xs = [F(c,depth) for c in cs]
    if any(cmp(a, b) >= 0 for a, b in zip(xs, xs[1:])):
        raise Undecided('terms not increasing')
    s3 = evalord.sup(xs)
    x4=F(induced(t, 4,depth),depth)
    s4 = evalord.sup(xs + [x4])
    if s3 is None or s4 is None or cmp(s3, s4):
        s3=fixedpoint_sup(xs)
        s4=fixedpoint_sup(xs+[x4])
    if s3 is None or s4 is None or cmp(s3, s4):
        raise Undecided('unstable sup')
    return s3


def seq(ts):
    names=ts.split() if isinstance(ts,str) else tuple(ts)
    def raw(name):
        if name in R:return R[name]
        if name.startswith('A'):
            k=int(name[1:]);return A0+(0,2)*k
        raise KeyError(name)
    return sum((raw(x) for x in names), ())


if __name__ == '__main__':
    BASE = (0,0,2,1) + seq(sys.argv[1])
    for w in sys.argv[2:]:
        try:
            print(w.ljust(30), show(F(seq(w))), flush=True)
        except (Undecided, TV.Unknown) as e:
            print(w.ljust(30), 'UNDECIDED', e, flush=True)
