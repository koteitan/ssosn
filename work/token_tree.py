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
    value = base
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
        if general and MOVABLE_ONE_EXPERIMENT and token.startswith('A'):
            end=len(copies)
            while end and copies[end-1]=='W':end-=1
            lower=end
            while lower and copies[lower-1]=='D':lower-=1
            if end<len(copies) and lower<end and lower and copies[lower-1]=='W' and k<end-lower:
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
        frame = Frame(token, k, copies, k, rank) if iterated and token.startswith('A') else None
        if frame:
            amount = CNF(tuple(replace(t, frame=frame) for t in amount.terms), origin)
        if token.startswith('A'):
            if k == 0:
                value = plus(value, amount, origin)
            elif fresh:
                seed_offset=offset
                if general and CUT_COPY_ACTION_EXPERIMENT:
                    actual_copy=fresh_copy_from_cut(tokens[:start+1],k)
                    seed_offset=typed_copy_rank(actual_copy,k-1,origin)
                value = plus(base, tower(plus(seed_offset, amount, origin), k, origin, frame), origin)
            else:
                value = bump(value, k, amount, origin)
            active_depth = k
        elif token == 'E1':
            if fresh:
                value = plus(base, epsilon(amount if iterated else ZERO, origin), origin)
            else:
                value = epsilon_iteration(value, active_depth, iterated, amount, origin)
        else:
            raise Unknown(('tree unsupported token', token))
        if movable_depth is not None:
            moved_origin=Origin('movable-one W', movable_depth, ('A'+str(movable_depth),),
                                tokens[:i], ('W',)*movable_iterations)
            value=bump(value, movable_depth, power(natural(movable_iterations,moved_origin),moved_origin),
                       moved_origin)
            active_depth=movable_depth
        fresh = False
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
    if CUT_COPY_ACTION_EXPERIMENT and u[:2]==(2,1):
        return epsilon(fold(parse(u[2:],True),general=True),Origin('cut copy action index'))
    try:
        return known_block_tree(u)
    except Unknown:
        if GENERAL_COPY_EXPERIMENT and u[:2]==(2,1):
            return epsilon(fold(parse(u[2:],True),general=True),Origin('general copy rank index'))
        raise


def block_value(u):
    return ordinal(block_tree(tuple(u)))


@lru_cache(maxsize=15000)
def body_tree(body):
    result = ZERO
    for unit in conj2.units(body):
        origin = Origin('structural unit', 0, (), unit)
        if unit == (0,):
            x = one(origin)
        elif unit == (2,):
            x = epsilon(ZERO, origin)
        else:
            t = conj2.T(unit)
            x = block_tree(unit) if t == unit else power(plus(one(origin), body_tree(t), origin), origin)
        result = plus(result, x, origin)
    return result


@lru_cache(maxsize=15000)
def value_tree(s):
    s = tuple(s)
    if s[:2] != (0,0) or max(s, default=0) > 2:
        raise Unknown('tree outside 0/1/2 range')
    origin = Origin('sequence', 0, (), s)
    if len(s)>2 and s[-1] == 0:
        return successor(value_tree(s[:-1]), origin)
    return plus(natural(2, origin), body_tree(s[2:]), origin)


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
