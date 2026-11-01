"""Recursive checker for Claude's four-case v2 upper-bound draft (§43).

The checker follows v_case_reduce43.py's 4,888 N=13 limit words.  It is a
bounded diagnostic, not a proof of the grammar or of the ordinal lemmas.

Run: timeout 600 python3 work/v_case_prove43.py [--tokens 15]
"""
import argparse
from collections import Counter
from functools import lru_cache
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import conj2
import ordinal
import v_bits43 as vb
import v_unit_shapes43 as shapes
from v_constraints_real43 import real_copy_word
from v_inequality43 import words_u


def rule(y, cls, s, n):
    """The three bit-copy forms, with n starting at 1."""
    y = tuple(y)
    if cls == 'R1':
        return y[:-1] + (1,) * (n + 1)
    if cls == 'R2':
        a = y[:-1]
        return a + ((0,) + a) * (n - 1)
    if cls == 'R3':
        h, q = y[:s], y[s + 1:-1]
        return h + ((0,) + q) * n
    raise ValueError(cls)


def spans(y):
    units = tuple(tuple(u) for u in conj2.units(tuple(y)))
    out, pos = [], 0
    for u in units:
        out.append((pos, pos + len(u)))
        pos += len(u)
    if pos != len(y):
        raise AssertionError(('units do not cover word', y, units))
    return units, tuple(out)


def class_and_start(word):
    real = tuple(real_copy_word(word, n) for n in (1, 2, 3))
    matches = shapes.match_classes(word, real)
    if not matches:
        raise ValueError(('no real-term class', word))
    r3 = [p for c, p in matches if c == 'R3']
    if r3:
        cls, pos = 'R3', max(r3)
        s = len(vb.bits(word[:pos]))
    else:
        cls, pos = matches[0]
        y = vb.bits(word)
        s = max(i for i, x in enumerate(y) if x == 2) if cls == 'R1' else 0
    return cls, s


def all_words(max_tokens):
    out = set()
    for core in words_u(max_tokens):
        if core[-1] not in shapes.LIMITS:
            continue
        for prefix in shapes.PREFIXES:
            out.add(prefix + core)
    return sorted(out, key=lambda w: (len(w), w))


def trailing_zero_case(y, cls, s):
    if cls == 'R2':
        a = tuple(y[:-1])
        return bool(a) and a[-1] == 0
    if cls == 'R3':
        q = tuple(y[s + 1:-1])
        return not q or q[-1] == 0
    return False


def case_of(y, cls, s, j):
    """Disjoint priority matching C4, C2, C1, then the C3 terminal case."""
    units, _ = spans(y)
    if trailing_zero_case(y, cls, s):
        return 'C4'
    if j != len(units) - 1:
        return 'C2'
    if cls == 'R1':
        u = tuple(units[-1])
        if u == (2,) or u[-2:] == (0, 2):
            reason, _ = c1_reduce(y, cls, s, j)
            if reason == 'C1-no-same-class-shift':
                return 'C3'
    return 'C1'


def top_exponent(x):
    """Return e when the leading CNF term of x is omega^e, if recognizable."""
    if not x:
        return None
    term = x[0]
    _, a, b = term
    e = b if not a else (term,)
    if ordinal.cmp(ordinal.w(e), (term,)) != 0:
        return None
    return e


def c4_check(y, cls, s, j):
    units, unit_spans = spans(y)
    # The measured split has the copy point at the start of its unit.
    if unit_spans[j][0] != s:
        return 'C4-copy-not-unit-start'
    if cls == 'R2':
        a = tuple(y[:-1])
        if not a or a[-1] != 0:
            return 'C4-R2-boundary'
        x = a[:-1]
        xu, _ = spans(x)
        expected = tuple(xu) + ((0,),)
        def expected_n(n):
            return (tuple(xu) + ((0,), (0,))) * (n - 1) + expected
    elif cls == 'R3':
        q = tuple(y[s + 1:-1])
        if q and q[-1] != 0:
            return 'C4-R3-boundary'
        x = (0,) + q
        xu, _ = spans(x)
        expected_n = lambda n: tuple(xu) * n
    else:
        return 'C4-wrong-class'

    xi = vb.v2(x)
    e = top_exponent(xi)
    if e is None:
        return 'C4-no-leading-omega-exponent'
    omega_e = ordinal.w(e)
    expected_parent = ordinal.w(ordinal.succ(e))
    parent_units = units[j:]
    parent_bits = tuple(bit for unit in parent_units for bit in unit)
    parent = vb.v2(parent_bits)
    if ordinal.cmp(parent, expected_parent) != 0:
        return 'C4-parent-not-omega-successor-exponent'

    # Six strict-below checks and six growth checks use terms through n=7.
    term_values = []
    for n in range(1, 8):
        yn = rule(y, cls, s, n)
        un, _ = spans(yn)
        if tuple(un[:j]) != tuple(units[:j]):
            return 'C4-prefix-changed'
        tail_units = un[j:]
        got_units = tuple(tuple(u) for u in tail_units)
        want_units = expected_n(n)
        if got_units != want_units:
            return 'C4-periodic-unit-shape'
        tail_bits = tuple(bit for unit in tail_units for bit in unit)
        value = vb.v2(tail_bits)
        if ordinal.cmp(value, parent) >= 0:
            return 'C4-term-not-below-parent'
        term_values.append(value)
    for left, right in zip(term_values[:6], term_values[1:]):
        if ordinal.cmp(right, ordinal.add(left, omega_e)) < 0:
            return 'C4-increment-too-small'
    return None


def epsilon_successor_form(x):
    """Return beta if x = epsilon_beta + 1, otherwise None."""
    if len(x) != 2 or x[-1] != ordinal.ONE[0]:
        return None
    head = x[0]
    _, a, beta = head
    if a != ordinal.ONE:
        return None
    if ordinal.cmp(ordinal.P(ordinal.ONE, beta), (head,)) != 0:
        return None
    return beta


def c3_check(y):
    units, _ = spans(y)
    u = tuple(units[-1])
    if u == (2,):
        value_anchor = ()
        xprime = ()
        make_um = lambda m: (1,) * (m + 1)
        expected_value = ordinal.P(ordinal.ONE, ordinal.ZERO)
        base_ok = ordinal.cmp(vb.v2(value_anchor), ordinal.ZERO) == 0 and ordinal.cmp(
            vb.v2(u), expected_value) == 0
        beta = None
    else:
        if len(u) < 2 or u[-2:] != (0, 2):
            return 'C3-shape'
        xprime = u[:-2]
        value_anchor = xprime + (0,)
        make_um = lambda m: xprime + (0,) + (1,) * (m + 1)
        beta = epsilon_successor_form(vb.v2(value_anchor))
        base_ok = beta is not None and ordinal.cmp(
            vb.v2(u), ordinal.P(ordinal.ONE, ordinal.succ(beta))) == 0
    if not base_ok:
        return 'C3-epsilon-value-identity'

    # Correct indexing: u_m=x'0 1^(m+1), m>=0.  T(u_0)=x'0,
    # then T(u_m)=u_(m-1) for m>=1.
    if tuple(conj2.T(make_um(0))) != value_anchor:
        return 'C3-bottom-T-step'
    for m in range(1, 7):
        if tuple(conj2.T(make_um(m))) != make_um(m - 1):
            return f'C3-T-step-m{m}'
    return None


def reducer(u):
    t = tuple(conj2.T(tuple(u)))
    if t != tuple(u):
        return 'T', t
    try:
        return 'T2', tuple(vb.T2(tuple(u)))
    except ValueError:
        return None, None


def allowed_starts(y, cls):
    if cls == 'R1':
        return [i for i, bit in enumerate(y) if bit == 2]
    if cls == 'R2':
        return [0]
    return [i for i, bit in enumerate(y) if bit == 0]


@lru_cache(maxsize=None)
def c1_reduce(y, cls, s, j):
    units, unit_spans = spans(y)
    lo = unit_spans[-1][0]
    u = tuple(units[-1])
    op, reduced = reducer(u)
    if op is None:
        return 'C1-no-T-or-T2-reduction', None
    rank_reduced = vb.v2(reduced)
    if op == 'T':
        predicted = ordinal.w(ordinal.add(ordinal.ONE, rank_reduced))
    else:
        predicted = ordinal.P(ordinal.ONE, rank_reduced)
    if ordinal.cmp(vb.v2(u), predicted) != 0:
        return 'C1-unit-value-identity', None

    # Reduce the changed last block of each real bit term, then seek a same-class
    # copy rule with shift d in {-1,0} on the shorter word.
    target_terms = []
    for n in range(1, 7):
        term_tail = tuple(rule(y, cls, s, n)[lo:])
        term_op, term_reduced = reducer(term_tail)
        if term_op is None:
            return f'C1-term-no-reduction-n{n}', None
        target_terms.append(term_reduced)

    found = []
    for d in (-1, 0):
        ns = [n for n in range(1, 7) if n + d >= 1]
        for s2 in allowed_starts(reduced, cls):
            try:
                if all(rule(reduced, cls, s2, n + d) == target_terms[n - 1]
                       for n in ns):
                    found.append((s2, d))
            except (IndexError, ValueError):
                pass
    if not found:
        return 'C1-no-same-class-shift', None
    # R1 is independent of s, so select the rightmost matching start.
    s2, d = max(found, key=lambda t: (t[0], t[1]))
    return None, (reduced, s2, d, op)


@lru_cache(maxsize=None)
def _prove(y, cls, s, active=()):
    y = tuple(y)
    key = (y, cls, s)
    if key in active:
        return False, 'cycle', ('cycle',)
    active = active + (key,)
    try:
        units, unit_spans = spans(y)
        if not units:
            return False, 'empty-word', ('base?',)
        j = next(i for i, (lo, hi) in enumerate(unit_spans) if lo <= s < hi)
    except (ValueError, StopIteration, IndexError):
        return False, 'bad-copy-position', ('pre',)

    # The prefix units before the copy point must be fixed by all six terms.
    for n in range(1, 7):
        try:
            term_units, _ = spans(rule(y, cls, s, n))
        except Exception as exc:
            return False, f'prefix-term-error-n{n}:{type(exc).__name__}', ('prefix',)
        if tuple(term_units[:j]) != tuple(units[:j]):
            return False, f'prefix-n{n}', ('prefix',)

    if y == (1,) and cls == 'R2':
        return True, None, ('base-R2-1',)
    if y == (2,) and cls == 'R1':
        return True, None, ('base-C3-2',)

    case = case_of(y, cls, s, j)
    if case == 'C4':
        reason = c4_check(y, cls, s, j)
        return reason is None, reason, ('C4',)
    if case == 'C3':
        reason = c3_check(y)
        return reason is None, reason, ('C3',)
    if case == 'C1':
        reason, next_data = c1_reduce(y, cls, s, j)
        if reason:
            return False, reason, ('C1',)
        reduced, s2, d, op = next_data
        ok, child_reason, child_route = _prove(reduced, cls, s2, active)
        route = ('C1-' + op + '-d' + str(d),) + child_route
        if not ok:
            return False, 'recursive:' + str(child_reason), route
        return True, None, route
    if case == 'C2':
        child = tuple(units[-1])
        child_cls, child_s = 'R2', 0
        ok, child_reason, child_route = _prove(child, child_cls, child_s, active)
        route = ('C2',) + child_route
        if not ok:
            return False, 'recursive:' + str(child_reason), route
        return True, None, route
    return False, 'unknown-case', (str(case),)


def prove(y, cls, s):
    """Return (success, failure_reason_or_None, recursive_route)."""
    return _prove(tuple(y), cls, s, ())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tokens', type=int, default=13)
    args = ap.parse_args()
    words = all_words(args.tokens)
    results = []
    routes = Counter()
    failures = Counter()
    failure_samples = {}
    route_ends = Counter()
    top_cases = Counter()
    depth_counts = Counter()
    case_depth_counts = Counter()
    successes = 0
    for word in words:
        cls, s = class_and_start(word)
        y = vb.bits(word)
        ok, reason, route = prove(y, cls, s)
        successes += int(ok)
        top_units, top_spans = spans(y)
        j = next(i for i, (lo, hi) in enumerate(top_spans) if lo <= s < hi)
        root_case = case_of(y, cls, s, j)
        top_cases[root_case] += 1
        nt = sum(x.startswith('C1-T-d') for x in route)
        nt2 = sum(x.startswith('C1-T2-d') for x in route)
        n2 = sum(x == 'C2' for x in route)
        depth = nt + nt2 + n2
        terminal = route[-1]
        routes[(nt, nt2, n2, terminal)] += 1
        route_ends[(root_case, terminal, ok)] += 1
        depth_counts[depth] += 1
        case_depth_counts[(root_case, depth)] += 1
        if not ok:
            reason_key = reason
            while reason_key.startswith('recursive:'):
                reason_key = reason_key[len('recursive:'):]
            failures[reason_key] += 1
            results.append((word, cls, s, y, reason, route))
            failure_samples.setdefault(reason_key, (word, cls, s, y, reason, route))
    results.sort(key=lambda row: (len(row[0]), row[0]))
    print('tokens', args.tokens, 'words', len(words))
    print('top-level cases', dict(top_cases))
    print('recursion depth distribution', dict(sorted(depth_counts.items())))
    print('case by recursion depth', {
        f'{case}/d{depth}': count
        for (case, depth), count in sorted(case_depth_counts.items())})
    print('route endings (root case, terminal, success):')
    for path, count in sorted(route_ends.items(), key=lambda kv: (-kv[1], kv[0])):
        print(' ', count, path)
    print('operation totals:', {
        'C1-T': sum(k[0] * v for k, v in routes.items()),
        'C1-T2': sum(k[1] * v for k, v in routes.items()),
        'C2': sum(k[2] * v for k, v in routes.items()),
    })
    print('recursive success', successes, 'failure', len(words) - successes)
    print('failures by reason', dict(failures))
    print('shortest failures (up to 5):')
    for word, cls, s, y, reason, route in results[:5]:
        print(' ', ''.join(word), 'bits=', ''.join(map(str, y)),
              'class=', cls, 's=', s, 'reason=', reason,
              'route=', ' > '.join(route))
    print('shortest failure by reason:')
    for reason_key, row in sorted(failure_samples.items()):
        word, cls, s, y, reason, route = row
        print(' ', reason_key, ''.join(word), 'bits=', ''.join(map(str, y)),
              'class=', cls, 's=', s, 'route=', ' > '.join(route))
    # Explain the C3 indexing issue with concrete evidence and corrected count.
    c3_examples = []
    for word in words:
        cls, s = class_and_start(word)
        y = vb.bits(word)
        units, unit_spans = spans(y)
        j = next(i for i, (lo, hi) in enumerate(unit_spans) if lo <= s < hi)
        if case_of(y, cls, s, j) != 'C3':
            continue
        u = tuple(units[-1])
        xprime = () if u == (2,) else u[:-2]
        value_anchor = () if u == (2,) else xprime + (0,)
        make_um = (lambda m: (1,) * (m + 1)) if u == (2,) else (
            lambda m: xprime + (0,) + (1,) * (m + 1))
        ok_steps = (tuple(conj2.T(make_um(0))) == value_anchor and
                    all(tuple(conj2.T(make_um(m))) == make_um(m-1)
                        for m in range(1, 7)))
        c3_examples.append((word, ok_steps))
    print('C3 corrected T-step diagnostic: words', len(c3_examples),
          'pass', sum(ok for _, ok in c3_examples))
    if c3_examples:
        word, corrected_ok = c3_examples[0]
        print(' C3 shortest', ''.join(word), 'corrected', corrected_ok)
        u = tuple(spans(vb.bits(word))[0][-1])
        xprime = () if u == (2,) else u[:-2]
        value_anchor = () if u == (2,) else xprime + (0,)
        make_um = (lambda m: (1,) * (m + 1)) if u == (2,) else (
            lambda m: xprime + (0,) + (1,) * (m + 1))
        print('  T(u0)=', conj2.T(make_um(0)), 'xprime0=', value_anchor,
              'T(u1)=', conj2.T(make_um(1)), 'u0=', make_um(0))


if __name__ == '__main__':
    main()
