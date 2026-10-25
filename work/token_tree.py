"""Experimental CNF-tree state, with token origins and retained copy stages.

No numeric token fold, rule6, lower, harness, or real-term recursion is used.
Ordinal tuples are an output/comparison format, never the state of a bump.
"""
import sys
from pathlib import Path
sys.path[:0] = [str(Path(__file__).resolve().parent), str(Path(__file__).resolve().parent.parent)]
from dataclasses import dataclass, replace, asdict
from functools import lru_cache, cached_property
import conj
import conj2
from ordinal import cmp, ZERO as OZERO, ONE as OONE
import token_base2
from cut_structure import CutTree


class Unknown(Exception):
    pass


@dataclass(frozen=True)
class Origin:
    token: str
    opened_depth: int = 0
    copy: tuple = ()
    source: tuple = ()
    iteration: tuple = ()


@dataclass(frozen=True)
class Frame:
    token: str
    opened_depth: int
    copy: tuple
    covered_depth: int
    rank: 'CNF | None' = None


@dataclass(frozen=True)
class CNF:
    terms: tuple
    origin: Origin

    @cached_property
    def ordinal(self):
        return tuple(('p', t.index.ordinal, t.argument.ordinal) for t in self.terms)


@dataclass(frozen=True)
class Principal:
    index: CNF
    argument: CNF
    origin: Origin
    frame: Frame | None = None


ROOT = Origin('zero')
ZERO = CNF((), ROOT)


def ordinal(tree):
    return tree.ordinal


def equal(a, b):
    return ordinal(a) == ordinal(b)


def phi(a, b, origin, frame=None):
    if len(b.terms) == 1 and cmp(ordinal(b.terms[0].index), ordinal(a)) > 0:
        return CNF(b.terms, origin)
    return CNF((Principal(a, b, origin, frame),), origin)


def power(b, origin, frame=None):
    return phi(ZERO, b, origin, frame)


def one(origin):
    return power(ZERO, origin)


def natural(n, origin):
    return CNF((Principal(ZERO, ZERO, origin),)*n, origin)


def plus(a, b, origin):
    if not b.terms:
        return CNF(a.terms, origin)
    head = ordinal(CNF((b.terms[0],), origin))
    k = len(a.terms)
    while k and cmp(ordinal(CNF((a.terms[k-1],), origin)), head) < 0:
        k -= 1
    return CNF(a.terms[:k] + b.terms, origin)


def successor(a, origin):
    return plus(a, one(origin), origin)


def omega(origin):
    return power(one(origin), origin)


def epsilon(b, origin, frame=None):
    return phi(one(origin), b, origin, frame)


def tower(seed, height, origin, frame=None):
    for _ in range(height):
        seed = power(seed, origin, frame)
    return seed


def next_fixed(level, x, origin):
    base = phi(level, ZERO, origin)
    if cmp(ordinal(x), ordinal(base)) < 0:
        return base
    term = x.terms[0]
    order = cmp(ordinal(term.index), ordinal(level))
    if order == 0:
        return phi(level, successor(term.argument, origin), origin)
    if order > 0:
        return phi(level, successor(x, origin), origin)
    return next_fixed(level, term.argument, origin)


def bump(tree, depth, amount, origin, absolute=0, requested=None):
    """Walk CNF nodes, retaining the frame at a freshly opened WD term."""
    if requested is None:
        requested = depth
    if depth == 0:
        return plus(tree, amount, origin)
    if not tree.terms:
        raise Unknown('empty tree at bumped depth')
    term = tree.terms[-1]
    pre = CNF(tree.terms[:-1], origin)
    frame = term.frame
    if frame is not None and 'D' in frame.copy and requested > frame.covered_depth:
        # The copied WD has rank omega. It is a logical seed, not another
        # exponent edge to traverse. Retain its scope after this promotion.
        promoted = replace(frame, covered_depth=requested)
        seed = plus(frame.rank if frame.rank is not None else omega(origin), amount, origin)
        return plus(pre, tower(seed, depth, origin, promoted), origin)
    exponent = term.argument if not term.index.terms else CNF((term,), term.origin)
    if not exponent.terms:
        n = 0
        while n < len(tree.terms) and ordinal(CNF((tree.terms[-1-n],), origin)) == OONE:
            n += 1
        seed = plus(natural(n, origin), amount, origin)
        return plus(CNF(tree.terms[:-n], origin), tower(seed, depth, origin, frame), origin)
    changed = bump(exponent, depth-1, amount, origin, absolute+1, requested)
    return plus(pre, power(changed, origin, frame), origin)


def epsilon_iteration(tree, depth, iterated, amount, origin):
    term = tree.terms[-1]
    pre = CNF(tree.terms[:-1], origin)
    if depth:
        exponent = term.argument if not term.index.terms else CNF((term,), term.origin)
        if not exponent.terms:
            raise Unknown('epsilon beyond opened tree')
        return plus(pre, power(epsilon_iteration(exponent, depth-1, iterated, amount, origin), origin), origin)
    fixed = next_fixed(one(origin), CNF((term,), term.origin), origin)
    q = fixed.terms[0].argument
    if iterated:
        q = plus(q, amount, origin)
    return plus(pre, epsilon(q, origin), origin)


def A(k):
    return (0,1,2)+(0,2)*k


W = A(0)+(1,)
BOUNDARY = (2,1,0,2)
GENERAL_COPY_EXPERIMENT = False  # rejected extension; use fresh caches when changing
MOVABLE_ONE_EXPERIMENT = False  # §18, independently guarded and checked
CUT_COPY_ACTION_EXPERIMENT = False  # §21; fresh structures and typed copy action
CONSISTENT_COPY_SEED_EXPERIMENT = False  # §27; fresh and promoted seeds use the depth-0 copy action
WD_AFTER_ITERATION_EXPERIMENT = False  # §28; trailing W after W D^b iterates A_b
RELTAIL_CAP_EXPERIMENT = False  # §31; measured common relative tails below their cap
RELTAIL_CAP_VALUES = None
RELTAIL_CAP_COUNTS = {'eligible': 0, 'table': 0, 'fallback': 0}
TAIL_S_EXPERIMENT = False  # §33; symbolic common-tail rule S, with seed fallback
TAIL_S_DEPTH_EXPERIMENT = False  # separate §33 extension to tails after fresh A_k
TAIL_S_MARKER_EXPERIMENT = False  # §34; value fresh siblings through their marker
TAIL_S_E_EXPERIMENT = False  # §35; value E by the sup of its A_n siblings
TAIL_S_COMPLETE_EXPERIMENT = False  # §36; S after every A_k sibling, with strict branch purity
TAIL_S_COUNTS = {'eligible': 0, 'decided': 0, 'undecided': 0}
TAIL_S_MARKER_COUNTS = {'eligible': 0, 'decided': 0, 'undecided': 0}
TAIL_S_E_COUNTS = {'eligible': 0, 'decided': 0, 'undecided': 0}
PURITY_TRACKING = False  # §35 measurement only; does not change values
PURE_BLOCKS = {}
PURE_BODIES = {}
PURE_VALUES = {}
PURE_FOLDS = {}
PURE_ANCHOR_TOKENS = set()
_TAIL_S_ACTIVE = False
_TAIL_S_MODULE = None


def _tail_undecided_total():
    return (TAIL_S_COUNTS['undecided'] + TAIL_S_MARKER_COUNTS['undecided']
            + TAIL_S_E_COUNTS['undecided'])


def _tail_s_fold(tokens, boundary, general):
    """Apply symbolic F to a unit tail; undecided F values use the seed fold."""
    global _TAIL_S_ACTIVE, _TAIL_S_MODULE
    if not TAIL_S_EXPERIMENT or not general or _TAIL_S_ACTIVE:
        return None
    tokens=tuple(tokens); j=0
    while j<len(tokens) and tokens[j] in ('W','D'):
        j+=1
    if j>=len(tokens) or not tokens[j].startswith('A'):
        return None
    k=int(tokens[j][1:]); tail=tokens[j+1:]
    if not tail and k==0:
        return None
    if k and not (TAIL_S_DEPTH_EXPERIMENT or TAIL_S_COMPLETE_EXPERIMENT):
        return None
    if tail:
        if tail[0] not in ('A'+str(k),'W'):
            return None
        marker=('W',)+tokens[:j]+('A'+str(k+1),)
        if raw_tokens(tail)>=raw_tokens(marker):
            return None
        if any(t.startswith('A') and int(t[1:])<k for t in tail):
            return None
    # The completed S experiment applies to every A_k unit.  Its tail must
    # remain below the next sibling marker at the same depth.
    if any(not (t in ('W','D') or t.startswith('A')) for t in tail):
        return None
    # F is common; the sibling itself is obtained from its marker.
    norm=tuple(('A'+str(int(t[1:])-k)) if t.startswith('A') else t for t in tail)
    if _TAIL_S_MODULE is None:
        import tail_symbolic as S
        _TAIL_S_MODULE=S
        S.BASE=(0,0,2,1)+(0,2)*10+(0,1,2)
        S.F.cache_clear()
    Fmod=_TAIL_S_MODULE
    def eval_F(word,depth=0):
        TAIL_S_COUNTS['eligible']+=1
        try:value=Fmod.F(Fmod.seq(word),depth=depth)
        except Exception:
            TAIL_S_COUNTS['undecided']+=1
            raise
        TAIL_S_COUNTS['decided']+=1
        return value
    sibling_relative=None
    try:
        relative=eval_F(norm,k) if tail else ()
    except Exception:return None
    _TAIL_S_ACTIVE=True
    try:
        base=fold(tokens[:j]+('A0',),boundary,general)
        if k:
            try:
                sibling_relative=eval_F(('W',)+tokens[:j]+(tokens[j],))
            except Exception:
                return None
            base=plus(base,_from_ordinal(sibling_relative,
                Origin('S sibling marker',k,(),('W',)+tokens[:j]+(tokens[j],))),
                Origin('S sibling base',k,(),tokens[:j+1]))
    finally:
        _TAIL_S_ACTIVE=False
    origin=Origin('symbolic common tail S',k,(),tokens,tuple(norm))
    amount=_from_ordinal(relative,origin)
    result=plus(base,amount,origin) if k==0 else bump(base,k,amount,origin)
    if PURITY_TRACKING:
        base_tokens=tuple(tokens[:j]+('A0',))
        PURE_FOLDS[tokens]=(PURE_FOLDS.get(base_tokens,False)
            and (not tail or relative is not None)
            and (not k or sibling_relative is not None))
    return result


def reltail_cap_load(path):
    """Load only tails whose 3/5/7-sample recursion stabilized."""
    import gzip, json
    global RELTAIL_CAP_VALUES
    data=json.load(gzip.open(path,'rt'))
    RELTAIL_CAP_VALUES={raw_tokens(tuple(row['tail'])):tuple(tuple(t) for t in row['value'])
        for row in data['rows'] if row['status']=='stable3_5_7' and 'value' in row
        and 'common-reference-language' in row['source']}
    return len(RELTAIL_CAP_VALUES)


def _from_ordinal(value, origin):
    return CNF(tuple(Principal(_from_ordinal(index,origin),_from_ordinal(argument,origin),origin)
                     for _,index,argument in value),origin)


def _reltail_cap_fold(tokens, boundary, general):
    """Apply the finite measured F table at the first unit after W/D roots."""
    if not RELTAIL_CAP_EXPERIMENT or not general or RELTAIL_CAP_VALUES is None:
        return None
    tokens=tuple(tokens);j=0
    while j<len(tokens) and tokens[j] in ('W','D'):j+=1
    if j>=len(tokens) or not tokens[j].startswith('A'):
        return None
    depth=int(tokens[j][1:]);tail=tokens[j+1:]
    if not tail or any(t not in ('A0','A1','A2','W','D') for t in tail):
        return None
    normalized=[]
    for t in tail:
        if t.startswith('A'):
            k=int(t[1:])-depth
            if k<0:return None
            normalized.append('A'+str(k))
        else:normalized.append(t)
    reference_marker=('W',)+('D',)*10+('A1',)
    if raw_tokens(tuple(normalized))>=raw_tokens(reference_marker):return None
    RELTAIL_CAP_COUNTS['eligible']+=1
    value=RELTAIL_CAP_VALUES.get(raw_tokens(tuple(normalized)))
    if value is None:
        RELTAIL_CAP_COUNTS['fallback']+=1
        return None
    RELTAIL_CAP_COUNTS['table']+=1
    prefix=fold(tokens[:j+1],boundary=boundary,general=general)
    origin=Origin('relative tail table',depth,(),tokens,tuple(normalized))
    amount=_from_ordinal(value,origin)
    return plus(prefix,amount,origin) if depth==0 else bump(prefix,depth,amount,origin)


def raw_tokens(tokens):
    return sum(((0,2) if t=='D' else W if t=='W' else
                A(int(t[1:]))+((1,) if t.startswith('E') else ()) for t in tokens),())


def fresh_copy_from_cut(tokens, k):
    """Rotate the actual raw B through terminal 01 to recover C A_(k-1)."""
    s=(0,0,2,1)+raw_tokens(tokens)
    c=CutTree.build(s).locate()['cut']
    b=s[c:-1]+(s[-1]-1,)
    v=(0,1)
    if (v+b)[-2:]!=v:
        raise Unknown('cut copy does not close at terminal 01')
    q=(v+b)[:-2]
    lower=A(k-1)
    if q[-len(lower):]!=lower:
        raise Unknown('cut copy lacks the lower-depth tail')
    return parse(q[:-len(lower)],True)


def typed_copy_rank(copies, depth, origin):
    """Candidate action on A_depth, distinct from its epsilon-index action.

    For one D-run, the checked movable-one law copies A_b when depth<b.
    Its omega iteration bumps that actual depth in the generated power tree.
    More complicated words retain the inherited, unproved rank hypothesis;
    the real-term checker must reject it if it violates order.
    """
    rank=copy_rank(copies)
    end=len(copies)
    while end and copies[end-1]=='W':end-=1
    lower=end
    while lower and copies[lower-1]=='D':lower-=1
    if end==len(copies) or lower==end or not lower or any(t!='W' for t in copies[:lower]):
        return rank
    b=end-lower
    if depth>=b:return rank
    baseline=power(copy_rank(copies[:end]),origin)
    moved=bump(baseline,b-depth,power(natural(len(copies)-end,origin),origin),origin)
    if len(moved.terms)!=1 or moved.terms[0].index.terms:
        raise Unknown('typed copy action is not one omega power')
    return moved.terms[0].argument


def parse(tail, allow_d=False):
    tail = tuple(tail)
    out = []
    while tail:
        if allow_d and tail[:2] == (0,2):
            out.append('D')
            tail = tail[2:]
            continue
        if tail[:3] != A(0):
            raise Unknown(('tree non-token suffix', tail))
        size, k = 3, 0
        while tail[size:size+2] == (0,2):
            size += 2
            k += 1
        if tail[size:size+1] == (1,):
            out.append('W' if k == 0 else 'E'+str(k))
            size += 1
        else:
            out.append('A'+str(k))
        tail = tail[size:]
    return tuple(out)


def base_index(j, origin):
    # The same law-derived induction bases as §16.1, not inferred outputs.
    return epsilon(ZERO if j == 0 else power(natural(j, origin), origin), origin)


def context_copy(tokens, start, k, beginning, default):
    """The syntactic L_A context, independent of numeric node values."""
    copies=default
    i=beginning
    while i<start:
        atom=tokens[i]
        i+=1
        unit_start=i
        while i<start and tokens[i] in ('W','D'):
            i+=1
        if atom.startswith('A') and int(atom[1:])<k and i>unit_start:
            copies=tokens[unit_start:i]
    return copies


def fold(tokens, boundary=False, general=False):
    tokens = tuple(tokens)
    symbolic=_tail_s_fold(tokens,boundary,general)
    if symbolic is not None:return symbolic
    relative=_reltail_cap_fold(tokens,boundary,general)
    if relative is not None:return relative
    j = 0
    if general:
        while j<len(tokens) and tokens[j] in ('W','D'):
            j+=1
    elif not boundary:
        while j < len(tokens) and tokens[j] == 'W':
            j += 1
    root_copy = ('W',)+tokens[:j] if general else ('W','D') if boundary else ('W',)*(j+1)
    root_origin = Origin('P' if boundary else 'leading W', 0, root_copy, tokens[:j])
    if general:
        rank=copy_rank(tokens[:j])
        base=epsilon(power(rank,root_origin),root_origin) if j else epsilon(ZERO,root_origin)
        offset=copy_rank(root_copy)
    elif boundary:
        base = epsilon(power(omega(root_origin), root_origin), root_origin)
        offset = omega(root_origin)
    else:
        base = base_index(j, root_origin)
        offset = natural(j+1, root_origin)
    def marker_relative(k):
        """Compute F(W Z A_k) for the fresh sibling marker."""
        global _TAIL_S_ACTIVE, _TAIL_S_MODULE
        if not (TAIL_S_EXPERIMENT and TAIL_S_MARKER_EXPERIMENT and general):
            return None
        marker=('W',)+tokens[:j]+('A'+str(k),)
        if _TAIL_S_MODULE is None:
            import tail_symbolic as S
            _TAIL_S_MODULE=S
            S.BASE=(0,0,2,1)+(0,2)*10+(0,1,2)
            S.F.cache_clear()
        TAIL_S_MARKER_COUNTS['eligible']+=1
        _TAIL_S_ACTIVE=True
        try:
            rel=_TAIL_S_MODULE.F(_TAIL_S_MODULE.seq(' '.join(marker)))
        except Exception:
            TAIL_S_MARKER_COUNTS['undecided']+=1
            return None
        finally:
            _TAIL_S_ACTIVE=False
        TAIL_S_MARKER_COUNTS['decided']+=1
        return _from_ordinal(rel,Origin('S sibling marker',0,(),marker))
    def e_sibling_sup(prefix):
        """Return the stable 3/4-sample sup of X A_n, for X E = sup X A_n."""
        if not (TAIL_S_EXPERIMENT and TAIL_S_MARKER_EXPERIMENT and TAIL_S_E_EXPERIMENT):
            return None
        TAIL_S_E_COUNTS['eligible']+=1
        try:
            xs=[ordinal(fold(tuple(prefix)+('A'+str(n),),boundary,general))
                for n in (1,2,3,4)]
            if any(cmp(a,b)>=0 for a,b in zip(xs,xs[1:])):
                raise Unknown('E siblings not increasing')
            s3=evalord.sup(xs[:3]);s4=evalord.sup(xs)
            if s3 is None or s4 is None or cmp(s3,s4):
                raise Unknown('E sibling sup undecided')
        except Exception:
            TAIL_S_E_COUNTS['undecided']+=1
            return None
        TAIL_S_E_COUNTS['decided']+=1
        return _from_ordinal(s4,Origin('S E sibling sup',0,(),tuple(prefix)))
    value = base
    pure = (tuple(tokens[:j]) in PURE_ANCHOR_TOKENS if j else True) if PURITY_TRACKING else False
    fresh, active_depth, i = True, 0, j
    while i < len(tokens):
        token = tokens[i]
        if token in ('W','D'):
            raise Unknown(('tree unattached operator', token))
        start = i
        i += 1
        m = 0
        while i < len(tokens) and tokens[i] == 'W':
            i += 1
            m += 1
        copies = ('W',)*m
        rank_limit = i < len(tokens) and tokens[i] == 'D'
        if rank_limit:
            if not m and not (general and token.startswith('E')):
                raise Unknown('tree D without iteration')
            copies += ('D',)
            i += 1
        if general:
            while i<len(tokens) and tokens[i] in ('W','D'):
                copies+=(tokens[i],)
                i+=1
        k = int(token[1:])
        # A terminal W after an internal one can iterate A_b rather than
        # increase the binary rank. Preserve the pre-W frame, then bump the
        # opened depth. The syntactic erasure law requires the preceding
        # A_k to have k<b; otherwise its whole unit is copied instead.
        movable_depth, movable_iterations = None, 0
        if general and (MOVABLE_ONE_EXPERIMENT or
                        WD_AFTER_ITERATION_EXPERIMENT and CUT_COPY_ACTION_EXPERIMENT
                        and CONSISTENT_COPY_SEED_EXPERIMENT) and token.startswith('A'):
            end=len(copies)
            while end and copies[end-1]=='W':end-=1
            lower=end
            while lower and copies[lower-1]=='D':lower-=1
            if (end<len(copies) and lower<end and lower and copies[lower-1]=='W' and k<end-lower
                    and (MOVABLE_ONE_EXPERIMENT or all(t=='W' for t in copies[:lower]))):
                movable_depth=end-lower
                movable_iterations=len(copies)-end
                copies=copies[:end]
        event_depth=k if token.startswith('A') else active_depth
        law_copy=context_copy(tokens,start,event_depth,j,root_copy)
        origin = Origin(token, event_depth, law_copy, tokens[:i], copies)
        rank=(typed_copy_rank(copies,k,origin) if CUT_COPY_ACTION_EXPERIMENT and token.startswith('A')
              else copy_rank(copies)) if general else None
        amount = power(rank if general else omega(origin) if rank_limit else natural(m, origin), origin)
        iterated=bool(copies) if general else m!=0
        frame_rank=(typed_copy_rank(copies,0,origin)
                    if general and CUT_COPY_ACTION_EXPERIMENT and CONSISTENT_COPY_SEED_EXPERIMENT
                    and iterated and token.startswith('A') else rank)
        frame = Frame(token, k, copies, k, frame_rank) if iterated and token.startswith('A') else None
        if frame:
            amount = CNF(tuple(replace(t, frame=frame) for t in amount.terms), origin)
        if token.startswith('A'):
            if k == 0:
                value = plus(value, amount, origin)
                if PURITY_TRACKING and (copies or rank_limit):
                    pure=False
            elif fresh:
                # The marker formula is for the exact fresh sibling Z A_k.
                # A_k followed by W/D is an iterated unit, not that sibling.
                relative=marker_relative(k) if not copies and not rank_limit else None
                if relative is not None:
                    value=plus(base,relative,origin)
                    if PURITY_TRACKING:
                        pure = pure and PURE_FOLDS.get(tuple(tokens[:j]+('A0',)),False)
                else:
                    seed_offset=offset
                    if general and CUT_COPY_ACTION_EXPERIMENT:
                        actual_copy=fresh_copy_from_cut(tokens[:start+1],k)
                        seed_offset=typed_copy_rank(actual_copy,0 if CONSISTENT_COPY_SEED_EXPERIMENT else k-1,origin)
                    value = plus(base, tower(plus(seed_offset, amount, origin), k, origin, frame), origin)
                    if PURITY_TRACKING:pure=False
            else:
                value = bump(value, k, amount, origin)
                if PURITY_TRACKING:pure=False
            active_depth = k
        elif token == 'E1':
            sibling=e_sibling_sup(tokens[:start])
            if sibling is not None:
                value=sibling
                if PURITY_TRACKING:
                    pure = pure and all(PURE_FOLDS.get(tuple(tokens[:start])+('A'+str(n),),False)
                                        for n in (1,2,3,4))
            elif fresh:
                value = plus(base, epsilon(amount if iterated else ZERO, origin), origin)
                if PURITY_TRACKING:pure=False
            else:
                value = epsilon_iteration(value, active_depth, iterated, amount, origin)
                if PURITY_TRACKING:pure=False
        else:
            raise Unknown(('tree unsupported token', token))
        if movable_depth is not None:
            moved_origin=Origin('movable-one W', movable_depth, ('A'+str(movable_depth),),
                                tokens[:i], ('W',)*movable_iterations)
            value=bump(value, movable_depth, power(natural(movable_iterations,moved_origin),moved_origin),
                       moved_origin)
            active_depth=movable_depth
            if PURITY_TRACKING:pure=False
        fresh = False
    if PURITY_TRACKING:
        PURE_FOLDS[tokens]=pure
    return value


def binary_index(bits, depth=0):
    """Build the base-(2) law's binary CNF tree without calling conj.v."""
    result = ZERO
    for unit in conj.units(bits):
        origin = Origin('A0' if unit == '0' else 'D', depth, ('A0',), tuple(bits))
        if unit == '0':
            x = one(origin)
        else:
            x = power(plus(one(origin), binary_index(conj.T(unit), depth+1), origin), origin)
        result = plus(result, x, origin)
    return result


def copy_rank(copies):
    """Hypothesis for the next scope: W/D copy words use the binary rank tree."""
    return binary_index(tuple(0 if token=='W' else 1 for token in copies))


def known_block_tree(u):
    u = tuple(u)
    binary = token_base2.parse(u)
    if binary is not None:
        origin = Origin('base (2) law', 0, ('A0',), binary)
        return epsilon(binary_index(binary), origin)
    if u == BOUNDARY:
        origin = Origin('W boundary', 0, ('W','D'))
        return epsilon(epsilon(power(omega(origin), origin), origin), origin)
    if u[:len(BOUNDARY)] == BOUNDARY:
        return epsilon(fold(parse(u[len(BOUNDARY):], True), True), Origin('boundary index'))
    if u[:2] == (2,1):
        return epsilon(fold(parse(u[2:])), Origin('token index'))
    raise Unknown(('tree unsupported base', u))


@lru_cache(maxsize=15000)
def block_tree(u):
    u=tuple(u)
    before=_tail_undecided_total()
    if CUT_COPY_ACTION_EXPERIMENT and u[:2]==(2,1):
        result=epsilon(fold(parse(u[2:],True),general=True),Origin('cut copy action index'))
    else:
        try:
            result=known_block_tree(u)
        except Unknown:
            if GENERAL_COPY_EXPERIMENT and u[:2]==(2,1):
                result=epsilon(fold(parse(u[2:],True),general=True),Origin('general copy rank index'))
            else:
                raise
    if PURITY_TRACKING:
        parsed=tuple(parse(u[2:],True)) if u[:2]==(2,1) else ()
        PURE_BLOCKS[u]=(parsed in PURE_ANCHOR_TOKENS or PURE_FOLDS.get(parsed,False))
    return result


def block_value(u):
    return ordinal(block_tree(tuple(u)))


@lru_cache(maxsize=15000)
def body_tree(body):
    body=tuple(body)
    before=_tail_undecided_total()
    children_pure=True
    result = ZERO
    for unit in conj2.units(body):
        origin = Origin('structural unit', 0, (), unit)
        if unit == (0,):
            x = one(origin)
        elif unit == (2,):
            x = epsilon(ZERO, origin)
        else:
            t = conj2.T(unit)
            if t == unit:
                x=block_tree(unit)
                children_pure=children_pure and PURE_BLOCKS.get(tuple(unit),not PURITY_TRACKING)
            else:
                x=power(plus(one(origin), body_tree(t), origin), origin)
                children_pure=children_pure and PURE_BODIES.get(tuple(t),not PURITY_TRACKING)
        result = plus(result, x, origin)
    if PURITY_TRACKING:
        PURE_BODIES[body]=children_pure and _tail_undecided_total()==before
    return result


@lru_cache(maxsize=15000)
def value_tree(s):
    s = tuple(s)
    if s[:2] != (0,0) or max(s, default=0) > 2:
        raise Unknown('tree outside 0/1/2 range')
    origin = Origin('sequence', 0, (), s)
    if len(s)>2 and s[-1] == 0:
        result=successor(value_tree(s[:-1]), origin)
        if PURITY_TRACKING:
            PURE_VALUES[s]=PURE_VALUES.get(s[:-1],not PURITY_TRACKING)
        return result
    result=plus(natural(2, origin), body_tree(s[2:]), origin)
    if PURITY_TRACKING:
        PURE_VALUES[s]=PURE_BODIES.get(tuple(s[2:]),not PURITY_TRACKING)
    return result


def value(s):
    return ordinal(value_tree(tuple(s)))


def dump(tree):
    return asdict(tree)


E0 = (('p', OONE, OZERO),)


if __name__=='__main__':
    from ordinal import show
    for text in sys.argv[1:]:
        try:print(text,show(value(tuple(map(int,text)))))
        except Unknown as exc:print(text,'UNKNOWN',exc)
