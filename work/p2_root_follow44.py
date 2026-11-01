"""Audit the flagged v7 block valuation on [P1,P2) (§44).

Run: timeout 900 python3 work/p2_root_follow44.py
"""
from collections import Counter
import json
import argparse
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import evalord
import harness
import p1_v_ext43
import p2_v3check44
import token_value
from ordinal import lt, show, succ

DATA = HERE / 'p2-tokens44-18.json'
OUT = HERE / 'p2-root-follow44.json'


def digits(raw):
    return ''.join(map(str, raw))


def set_mode(p2):
    token_value.P1_ROOT_EXPERIMENT = True
    token_value.P1_V_BITS_EXPERIMENT = True
    token_value.P1_V_FOLD_EXPERIMENT = False
    token_value.P1_V_RAW_EXPERIMENT = False
    token_value.P2_V7_EXPERIMENT = p2


def clear_caches():
    for name in ('value', 'body_value', 'block_value', 'index', 'parse_p2_v7_copies',
                 'p1_v_anchor'):
        fn = getattr(token_value, name, None)
        if fn is not None and hasattr(fn, 'cache_clear'):
            fn.cache_clear()
    if 'token_tree' in sys.modules:
        mod = sys.modules['token_tree']
        for name in ('value', 'value_tree', 'body_tree', 'block_tree',
                     'body_value', 'block_value', 'index'):
            fn = getattr(mod, name, None)
            if fn is not None and hasattr(fn, 'cache_clear'):
                fn.cache_clear()


def get_value(raw):
    try:
        return token_value.value(tuple(raw))
    except (token_value.Unknown, RecursionError, ValueError):
        return None


def short_key(row):
    raw = row.get('raw', row.get('left', ''))
    other = row.get('right', '')
    return (len(raw), raw, len(other), other, row.get('n', 0))


def compare_p_interval():
    """Check P-side values in fresh caches with P2 flag off and on."""
    forms = p1_v_ext43.enumerate_forms(20)
    results = []
    for flag in (False, True):
        set_mode(flag)
        clear_caches()
        vals = {raw: get_value(raw) for raw in forms}
        results.append(vals)
    off, on = results
    changed = []
    for raw in forms:
        a, b = off[raw], on[raw]
        if a != b:
            changed.append({
                'raw': digits(raw),
                'off': None if a is None else show(a),
                'on': None if b is None else show(b),
            })
    return {
        'forms': len(forms),
        'off_decided': sum(v is not None for v in off.values()),
        'on_decided': sum(v is not None for v in on.values()),
        'changed': len(changed),
        'shortest_changes': sorted(changed, key=lambda x: (len(x['raw']), x['raw']))[:10],
    }


def run_p2():
    data = json.loads(DATA.read_text())
    words = sorted(tuple(map(int, raw)) for raw in data['standard_raw'])
    set_mode(True)
    clear_caches()
    counts = Counter(forms=len(words))
    values = {}
    unknowns = []
    succ_issues = []
    term_unknowns = []
    term_not_below = []
    sup_diffs = {k: [] for k in (3, 6, 10)}
    rows = []
    started = time.monotonic()

    for raw in words:
        val = get_value(raw)
        values[raw] = val
        spelling = digits(raw)
        if val is None:
            counts['unknown'] += 1
            if len(unknowns) < 10000:
                unknowns.append({'raw': spelling})
            continue
        counts['decided'] += 1
        row = {'raw': spelling, 'value': show(val)}
        if raw[-1] == 0:
            par = get_value(raw[:-1])
            if par is None:
                counts['successor_parent_unknown'] += 1
            elif val == succ(par):
                counts['successor_agree'] += 1
            else:
                counts['successor_differ'] += 1
                succ_issues.append({'raw': spelling, 'parent': show(par), 'value': show(val)})
            rows.append(row)
            continue

        counts['limit'] += 1
        xs = []
        term_spellings = []
        for n in range(1, 11):
            term = tuple(harness.fs(raw, n))
            tv = get_value(term)
            xs.append(tv)
            term_spellings.append(digits(term))
            if tv is None:
                counts['limit_term_unknown_total'] += 1
                if len(term_unknowns) < 10000:
                    term_unknowns.append({'raw': spelling, 'n': n, 'term': digits(term)})
            elif lt(tv, val):
                counts['term_below_parent_total'] += 1
            else:
                counts['term_not_below_parent'] += 1
                row.setdefault('not_below', []).append({'n': n, 'value': show(tv)})
                if len(term_not_below) < 10000:
                    term_not_below.append({'raw': spelling, 'n': n, 'term': digits(term),
                                           'term_value': show(tv), 'parent_value': show(val)})
        row['terms'] = term_spellings
        row['all10_decided'] = all(x is not None for x in xs)
        counts['limit_all10_decided' if row['all10_decided'] else 'limit_not_all10_decided'] += 1
        for k in (3, 6, 10):
            prefix = xs[:k]
            if any(x is None for x in prefix):
                counts[f'sup{k}_unknown'] += 1
                continue
            try:
                sup = evalord.sup(prefix)
            except (RecursionError, ValueError):
                sup = None
            if sup is None:
                counts[f'sup{k}_unknown'] += 1
            elif sup == val:
                counts[f'sup{k}_agree'] += 1
            else:
                counts[f'sup{k}_differ'] += 1
                row[f'sup{k}'] = show(sup)
                if len(sup_diffs[k]) < 10000:
                    sup_diffs[k].append({'raw': spelling, 'parent': show(val),
                                         'sup': show(sup)})
        rows.append(row)

    # Adjacent order among all decided standard forms, in raw lexicographic order.
    ordered = [(raw, values[raw]) for raw in words if values[raw] is not None]
    inversions = []
    for (a, av), (b, bv) in zip(ordered, ordered[1:]):
        if not lt(av, bv):
            counts['adjacent_order_inversion'] += 1
            inversions.append({'left': digits(a), 'left_value': show(av),
                               'right': digits(b), 'right_value': show(bv)})

    examples = {
        'unknown': sorted(unknowns, key=short_key)[:5],
        'successor_differ': sorted(succ_issues, key=short_key)[:5],
        'term_not_below_parent': sorted(term_not_below, key=short_key)[:5],
        'sup3_differ': sorted(sup_diffs[3], key=short_key)[:5],
        'sup6_differ': sorted(sup_diffs[6], key=short_key)[:5],
        'sup10_differ': sorted(sup_diffs[10], key=short_key)[:5],
        'adjacent_order_inversion': sorted(inversions, key=short_key)[:5],
        'term_unknown': sorted(term_unknowns, key=short_key)[:5],
    }
    ordered_inversions = sorted(inversions,
                                key=lambda x: (len(x['left']), x['left'],
                                               len(x['right']), x['right']))
    return {
        'range': '[P1,P2)', 'max_raw_length': 18, 'max_terms': 10,
        'flags': ['P1_ROOT_EXPERIMENT', 'P1_V_BITS_EXPERIMENT', 'P2_V7_EXPERIMENT'],
        'counts': dict(counts), 'examples': examples,
        'adjacent_order': {
            'valued_count': len(ordered),
            'inversion_count': len(inversions),
            'shortest_inversions': ordered_inversions[:20],
        },
        'rows': rows,
        'elapsed_seconds': round(time.monotonic() - started, 2),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--order-only', action='store_true',
                    help='recompute only the adjacent lexicographic order audit')
    args = ap.parse_args()
    start = time.monotonic()
    if args.order_only:
        data = json.loads(DATA.read_text())
        words = sorted(tuple(map(int, raw)) for raw in data['standard_raw'])
        set_mode(True)
        clear_caches()
        vals = [(raw, get_value(raw)) for raw in words]
        vals = [(raw, val) for raw, val in vals if val is not None]
        inversions = []
        for (left, lv), (right, rv) in zip(vals, vals[1:]):
            if not lt(lv, rv):
                inversions.append({'left': digits(left), 'left_value': show(lv),
                                   'right': digits(right), 'right_value': show(rv)})
        print('forms', len(words), 'decided', len(vals), 'lex_inversions', len(inversions))
        shortest = sorted(inversions,
                          key=lambda x: (len(x['left']), x['left'],
                                         len(x['right']), x['right']))
        print('shortest', shortest[:10])
        if OUT.exists():
            report = json.loads(OUT.read_text())
            report['p2']['counts']['adjacent_order_inversion'] = len(inversions)
            report['p2']['examples']['adjacent_order_inversion'] = shortest[:5]
            report['p2']['adjacent_order'] = {
                'valued_count': len(vals), 'inversion_count': len(inversions),
                'shortest_inversions': shortest[:20],
            }
            OUT.write_text(json.dumps(report, ensure_ascii=False,
                                      separators=(',', ':')) + '\n')
            print('updated', OUT)
        return
    p1_check = compare_p_interval()
    p2 = run_p2()
    report = {'p_interval_unchanged': p1_check, 'p2': p2,
              'elapsed_seconds': round(time.monotonic() - start, 2)}
    OUT.write_text(json.dumps(report, ensure_ascii=False, separators=(',', ':')) + '\n')
    print('P interval', p1_check)
    print('P2 counts', p2['counts'])
    print('P2 examples', p2['examples'])
    print('saved', OUT, OUT.stat().st_size, 'bytes; elapsed', report['elapsed_seconds'])


if __name__ == '__main__':
    main()
