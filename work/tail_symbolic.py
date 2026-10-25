"""Symbolic tail values F after a unit (2026-10-25, Claude). Experimental, hypothesis S.

For a tail T after the base X⌢A0, the contracted real terms have the form T[n] = H Q^(n-1) V.
- T ends with A0:            F(T) = F(T minus A0) + 1.
- Q = A1 R, R without A0 (hypothesis S): each block adds 1+F(R) at depth 1, so
                             F(T) = bump_last(F(H), 1, (1+F(R))·ω).
- other Q:                   F(T) = sup of F(T[1..3]) (evalord.sup, checked with T[4]).
Only H and R (shorter) or T[n] are consulted. Values are relative to the base.
usage: python3 work/tail_symbolic.py "D D D A0" "W D D" "W D W D" ...
"""
import os, sys, gzip, pickle
from pathlib import Path
sys.path[:0] = [os.path.dirname(os.path.abspath(__file__)), os.path.dirname(os.path.dirname(os.path.abspath(__file__)))]
import harness, evalord
import token_value as TV
from ordinal import ZERO, ONE, OMEGA, P, add, cmp, fs, is_limit, show
sys.setrecursionlimit(100000)
R = {'A0': (0,1,2), 'A1': (0,1,2,0,2), 'A2': (0,1,2,0,2,0,2), 'W': (0,1,2,1), 'D': (0,2)}
A0, A1 = (0,1,2), (0,1,2,0,2)
BASE = None
FIXEDPOINT_SUP_EXPERIMENT = False  # §38; fixed-point-aware 3/4-term sup
CURRENT_BUDGET_SECONDS = 0.0  # runner sets this only for budgeted experiments
_CACHE_VERSION = 2  # s_block_k changes the value of cached F terms
_F_CACHE = {}
_INDUCED_CACHE = {}
_PERIODIC_CACHE = {}
CACHE_STATS = {'F_hit': 0, 'F_miss': 0, 'F_timeout_hit': 0,
               'induced_hit': 0, 'induced_miss': 0,
               'periodic_hit': 0, 'periodic_miss': 0}


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
    key=(BASE,t,n,depth)
    hit=_INDUCED_CACHE.get(key)
    if hit is not None:
        CACHE_STATS['induced_hit']+=1
        if hit[0]=='error':raise Undecided(hit[1])
        return hit[1]
    CACHE_STATS['induced_miss']+=1
    try:value=_induced_uncached(t,n,depth)
    except Undecided as e:
        _INDUCED_CACHE[key]=('error',str(e))
        raise
    _INDUCED_CACHE[key]=('value',value)
    return value


def _induced_uncached(t, n, depth):
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
    key=(BASE,t,depth)
    hit=_PERIODIC_CACHE.get(key)
    if hit is not None:
        CACHE_STATS['periodic_hit']+=1
        if hit[0]=='error':raise Undecided(hit[1])
        return hit[1]
    CACHE_STATS['periodic_miss']+=1
    try:value=_periodic_uncached(t,depth)
    except Undecided as e:
        _PERIODIC_CACHE[key]=('error',str(e))
        raise
    _PERIODIC_CACHE[key]=('value',value)
    return value


def _periodic_uncached(t, depth):
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
    return s_block_k(Q) is not None


def s_block_k(Q):
    """(k, shifted R) when Q = A_k R, k >= 1, and R stays at depth >= k (no A_j with j < k).
    Inside R, A_j is +1 at depth j, i.e. the common-language A_(j-k), so R is shifted by k."""
    if Q[:3] != A0:
        return None
    j = 3; k = 0
    while Q[j:j+2] == (0, 2):
        j += 2; k += 1
    if k == 0 or Q[j:j+1] == (1,):
        return None
    r = tokens(Q[j:])
    if r is None:
        return None
    out = []
    for t in r:
        if t[0] == 'A':
            i = int(t[1:])
            if i < k:
                return None
            out.append('A%d' % (i - k))
        else:
            out.append(t)
    return k, sum((R[t] if t in R else (0, 1, 2) + (0, 2) * int(t[1:]) for t in out), ())


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


def fixedpoint_sup(xs, K=None):
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
        if checked_limit(a,xs,K=max(4,len(xs)-1) if K is None else K):return a
    return None


def F(t, depth=0):
    key=(BASE,FIXEDPOINT_SUP_EXPERIMENT,t,depth)
    hit=_F_CACHE.get(key)
    if hit is not None:
        CACHE_STATS['F_hit']+=1
        if hit[0]=='error':raise Undecided(hit[1])
        if hit[0]=='timeout':
            if CURRENT_BUDGET_SECONDS<=hit[1]:
                CACHE_STATS['F_timeout_hit']+=1
                raise Undecided('cached F time budget exceeded')
            del _F_CACHE[key]
        else:return hit[1]
    CACHE_STATS['F_miss']+=1
    try:value=_F_uncached(t,depth)
    except (Undecided,TV.Unknown) as e:
        if str(e)=='cached F time budget exceeded' and CURRENT_BUDGET_SECONDS>0:
            _F_CACHE[key]=('timeout',CURRENT_BUDGET_SECONDS)
        else:
            _F_CACHE[key]=('error',str(e))
        raise
    except BaseException as e:
        if type(e).__name__=='CaseTimeout' and CURRENT_BUDGET_SECONDS>0:
            _F_CACHE[key]=('timeout',CURRENT_BUDGET_SECONDS)
        raise
    _F_CACHE[key]=('value',value)
    return value


def _F_uncached(t, depth):
    if not t:
        return ZERO
    if t[-3:] == A0:
        return add(F(t[:-3],depth), ONE)
    H, Q, V, cs = periodic(t,depth)
    blk = s_block_k(Q)
    if blk is not None:
        k, r = blk
        step = add(ONE, F(r,depth))
        amount = mul_omega(step)
        return TV.bump_last(F(H,depth), k, amount)
    xs = [F(c,depth) for c in cs]
    if any(cmp(a, b) >= 0 for a, b in zip(xs, xs[1:])):
        raise Undecided('terms not increasing')
    s3 = evalord.sup(xs)
    x4=F(induced(t, 4,depth),depth)
    s4 = evalord.sup(xs + [x4])
    if FIXEDPOINT_SUP_EXPERIMENT and (s3 is None or s4 is None or cmp(s3, s4)):
        s3=fixedpoint_sup(xs)
        s4=fixedpoint_sup(xs+[x4])
    if FIXEDPOINT_SUP_EXPERIMENT and (s3 is None or s4 is None or cmp(s3,s4)):
        # The candidate is accepted only when the initial three and four
        # samples independently identify the same fixed point. Later rolling
        # windows can have false plateaus before crossing a larger epsilon.
        a=evalord.sup(xs) or fixedpoint_sup(xs,K=2)
        b=evalord.sup(xs+[x4]) or fixedpoint_sup(xs+[x4],K=3)
        if a is not None and b is not None and cmp(a,b)==0:
            return a
    if s3 is None or s4 is None or cmp(s3, s4):
        raise Undecided('unstable sup')
    return s3


def clear_caches():
    _F_CACHE.clear();_INDUCED_CACHE.clear();_PERIODIC_CACHE.clear()
    for key in CACHE_STATS:CACHE_STATS[key]=0


def load_cache(path):
    path=Path(path)
    if not path.exists():return (0,0,0)
    with gzip.open(path,'rb') as f:data=pickle.load(f)
    if data.get('version')!=_CACHE_VERSION:raise ValueError('tail cache version mismatch')
    for key, incoming in data['F'].items():
        if incoming==('error','cached F time budget exceeded'):
            continue  # An older runner saved a budgeted miss as permanent.
        old=_F_CACHE.get(key)
        if old is None or (incoming[0]=='value' and old[0]!='value') or (
            incoming[0]=='timeout' and old[0]=='timeout' and incoming[1]>old[1]):
            _F_CACHE[key]=incoming
    _INDUCED_CACHE.update(data['induced'])
    _PERIODIC_CACHE.update(data['periodic'])
    return (len(data['F']),len(data['induced']),len(data['periodic']))


def save_cache(path):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    pending=path.with_name(path.name+'.pending')
    data={'version':_CACHE_VERSION,'F':_F_CACHE,'induced':_INDUCED_CACHE,
          'periodic':_PERIODIC_CACHE}
    with gzip.open(pending,'wb',compresslevel=3) as f:
        pickle.dump(data,f,protocol=pickle.HIGHEST_PROTOCOL)
    pending.replace(path)
    return (len(_F_CACHE),len(_INDUCED_CACHE),len(_PERIODIC_CACHE))


F.cache_clear=clear_caches


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
