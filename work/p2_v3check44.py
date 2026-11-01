"""Measure the tentative 3-bit valuation on the P1 interval.

Run: timeout 600 python3 work/p2_v3check44.py
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
import p1_tokens43 as p1
import v_bits44
from ordinal import cmp, lt, show, succ, w

P1 = (0, 0, 2, 1, 0, 2, 1)
BASE = (0, 0, 2, 1)
DATA = HERE / 'p2-tokens44-18.json'
OUTS = {'v3': HERE / 'p2-v3check44.json',
        'v4': HERE / 'p2-v4check44.json',
        'v6': HERE / 'p2-v6check44.json',
        'v7': HERE / 'p2-v7check44.json'}
MAXLEN = 18
COPY = frozenset(('W', 'D', 'V'))


def parse_suffix(raw, token_map):
    """All normalized parses of a suffix, preserving ambiguity for auditing."""
    forms = p1.parse_all(tuple(raw), token_map, cap=10000)
    return sorted({p1.normalize_tokens(form) for form in forms})


def ordinal_value(tokens, rank):
    if rank == 'v3':
        return v_bits44.B(tuple(tokens))
    if rank == 'v4':
        return v_bits44.B4(tuple(tokens))
    if rank == 'v6':
        return v_bits44.v6(v_bits44.bits6(tuple(tokens)))
    if rank == 'v7':
        return v_bits44.B7(tuple(tokens))
    raise ValueError(rank)


def value_text(tokens, rank):
    try:
        return show(ordinal_value(tokens, rank)), None
    except (v_bits44.Unknown, RecursionError) as exc:
        return None, str(exc)


def term_tokens(raw, token_map):
    """Recognize c, c L1, or c Z after the common (0,0,2,1) prefix."""
    raw = tuple(raw)
    if raw[:len(BASE)] != BASE:
        return None, 'wrong_base'
    parses = parse_suffix(raw[len(BASE):], token_map)
    matches = []
    for form in parses:
        if form and form[-1] == 'Z':
            core, ending = form[:-1], 'Z'
        elif form and form[-1] == 'L1':
            core, ending = form[:-1], 'L1'
        else:
            core, ending = form, 'plain'
        if core and all(t in COPY for t in core):
            matches.append((tuple(core), ending))
    matches = sorted(set(matches))
    if len(matches) != 1:
        return None, 'no_supported_parse' if not matches else 'ambiguous_supported_parse'
    return matches[0], None


def value_of_term(raw, token_map, rank):
    parsed, reason = term_tokens(raw, token_map)
    if parsed is None:
        return None, reason, None
    core, ending = parsed
    try:
        if rank == 'v6':
            base_value = v_bits44.B6_copy(tuple(core))
        elif rank == 'v7':
            base_value = v_bits44.B7(tuple(core))
        else:
            base_value = ordinal_value(core, rank)
        if ending == 'L1':
            value = w(succ(base_value))
        elif ending == 'Z':
            value = succ(base_value)
        else:
            value = base_value
        return value, None, {'tokens': list(core), 'ending': ending}
    except (v_bits44.Unknown, RecursionError) as exc:
        return None, str(exc), {'tokens': list(core), 'ending': ending}


def ordinal_sup(values):
    if not values or any(value is None for value in values):
        return None
    try:
        return evalord.sup(values)
    except (RecursionError, ValueError):
        return None


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--rank', choices=('v3', 'v4', 'v6', 'v7'), default='v3')
    args = ap.parse_args()
    rank = args.rank
    out_path = OUTS[rank]
    start = time.monotonic()
    expected_v6 = {
        ('V',): 'z0',
        ('V', 'W'): 'z0+1',
        ('V', 'D'): 'e_(z0+w)',
        ('V', 'W', 'V'): 'e_(z0+1)',
        ('V', 'V'): 'h0',
        ('V', 'D', 'V', 'V', 'D'): 'z_w',
    }
    expected_v7 = {
        ('V',): 'z0',
        ('V', 'D'): 'z0+e_w',
        ('V', 'W'): 'z0+e0+1',
        ('V', 'W', 'V'): 'z0+e1',
        ('V', 'W', 'D'): 'z0+w^(e0+1)',
        ('V', 'D', 'V', 'V', 'D'): 'z_w',
        ('V', 'D', 'D'): 'z0+e_w^w',
    }
    if rank == 'v6':
        print('v6 expected-value checks')
        for tokens, expected in expected_v6.items():
            actual = show(v_bits44.v6(v_bits44.bits6(tokens)))
            print(''.join(tokens), actual, 'expected', expected)
            if actual != expected:
                raise AssertionError(('v6 expectation mismatch', tokens,
                                      expected, actual))
    if rank == 'v7':
        print('v7 expected-value checks')
        for tokens, expected in expected_v7.items():
            actual = show(v_bits44.v7(tokens))
            print(''.join(tokens), actual, 'expected', expected)
            if actual != expected:
                raise AssertionError(('v7 expectation mismatch', tokens,
                                      expected, actual))
        mixed = show(v_bits44.v7(('V', 'V', 'W', 'V')))
        mixed_expected = 'h0+e_(z0+1)'
        print('VVWV (bits 3R 0 2)', mixed, 'expected', mixed_expected)
        if mixed != mixed_expected:
            raise AssertionError(('v7 mixed-head expectation mismatch', mixed))
    if rank == 'v4':
        mixed = show(v_bits44.v4((3, 0, 2)))
        mixed_expected = 'e_(z0+1)'
        print('v4(3 0 2)', mixed, 'expected', mixed_expected)
        if mixed != mixed_expected:
            raise AssertionError(('v4 mixed-head expectation mismatch', mixed))
    token_map = p1.token_map(MAXLEN)
    token_map.update({'Z': (0,), 'L1': (0, 1)})
    for token in ('W', 'D', 'V'):
        if token not in token_map:
            raise AssertionError(token)
    data = json.loads(DATA.read_text())
    parents = []
    counts = Counter()
    unknown_examples = []
    term_issue_examples = []
    term_above_examples = []
    sup3_diff_examples = []
    sup6_diff_examples = []
    rows = []

    for spelling in data['standard_raw']:
        raw = tuple(map(int, spelling))
        if len(raw) > MAXLEN or raw[:len(P1)] != P1:
            continue
        suffix = raw[len(P1):]
        forms = parse_suffix(suffix, token_map)
        copy_forms = [form for form in forms if all(t in COPY for t in form)]
        if len(copy_forms) != 1:
            counts['not_single_WDV_suffix'] += 1
            continue

        tail = copy_forms[0]
        c = ('V',) + tuple(tail)
        try:
            parent = ordinal_value(c, rank)
            parent_error = None
        except (v_bits44.Unknown, RecursionError) as exc:
            parent = None
            parent_error = str(exc)
        row = {
            'raw': spelling,
            'tokens_after_P1': list(tail),
            'copy_word_including_root_V': list(c),
            'parent_value': None if parent is None else show(parent),
            'parent_unknown': parent_error,
            'kind': 'successor' if raw and raw[-1] == 0 else 'limit',
            'terms': [],
            'sup3': None,
            'sup6': None,
        }
        counts['candidate_words'] += 1
        if parent is None:
            counts['parent_unknown'] += 1
            if len(unknown_examples) < 10000:
                unknown_examples.append({'raw': spelling, 'where': 'parent',
                                         'reason': parent_error})
        else:
            parents.append((raw, parent, row))

        if row['kind'] == 'limit':
            term_values = []
            for n in range(1, 7):
                term = tuple(harness.fs(raw, n))
                value, reason, description = value_of_term(term, token_map, rank)
                term_values.append(value)
                row['terms'].append({
                    'n': n,
                    'raw': ''.join(map(str, term)),
                    'tokens': description,
                    'value': None if value is None else show(value),
                    'unknown': reason,
                })
                counts['limit_terms'] += 1
                if value is None:
                    counts['unknown_terms'] += 1
                    if len(unknown_examples) < 10000:
                        unknown_examples.append({'raw': spelling, 'term_n': n,
                                                 'term_raw': ''.join(map(str, term)),
                                                 'reason': reason})
                    if len(term_issue_examples) < 10000:
                        term_issue_examples.append({'raw': spelling, 'term_n': n,
                                                    'term_raw': ''.join(map(str, term)),
                                                    'reason': reason})
                elif parent is not None:
                    if lt(value, parent):
                        counts['term_below_parent'] += 1
                    elif value == parent:
                        counts['term_equal_parent'] += 1
                        counts['term_not_below_parent'] += 1
                        if len(term_above_examples) < 10000:
                            term_above_examples.append({
                                'raw': spelling, 'term_n': n,
                                'term_raw': ''.join(map(str, term)),
                                'term_value': show(value), 'parent_value': show(parent),
                                'comparison': 'equal'})
                    else:
                        counts['term_above_parent'] += 1
                        counts['term_not_below_parent'] += 1
                        if len(term_above_examples) < 10000:
                            term_above_examples.append({
                                'raw': spelling, 'term_n': n,
                                'term_raw': ''.join(map(str, term)),
                                'term_value': show(value), 'parent_value': show(parent),
                                'comparison': 'greater'})
            row['all_6_terms_decided'] = all(v is not None for v in term_values)
            if row['all_6_terms_decided']:
                for k in (3, 6):
                    value = ordinal_sup(term_values[:k])
                    row[f'sup{k}'] = None if value is None else show(value)
                    if value is None:
                        counts[f'sup{k}_undecided'] += 1
                    elif parent is None:
                        counts[f'sup{k}_parent_unknown'] += 1
                    elif value == parent:
                        counts[f'sup{k}_agrees'] += 1
                    else:
                        counts[f'sup{k}_differs'] += 1
                        target = sup3_diff_examples if k == 3 else sup6_diff_examples
                        if len(target) < 10000:
                            target.append({'raw': spelling,
                                           'sup': show(value),
                                           'parent': show(parent)})
            else:
                counts['sup3_undecided'] += 1
                counts['sup6_undecided'] += 1
        else:
            row['parent_successor_value'] = None if parent is None else show(succ(parent))
        rows.append(row)

    # Adjacent-order audit among candidate parent values.
    parents.sort(key=lambda item: item[0])
    inversions = []
    for left, right in zip(parents, parents[1:]):
        if not lt(left[1], right[1]):
            inversions.append({
                'left_raw': ''.join(map(str, left[0])),
                'left_value': show(left[1]),
                'right_raw': ''.join(map(str, right[0])),
                'right_value': show(right[1]),
            })
    inversions.sort(key=lambda x: (len(x['left_raw']) + len(x['right_raw']),
                                   x['left_raw'], x['right_raw']))

    report = {
        'range': '[P1,P2)',
        'max_raw_length': MAXLEN,
        'rank': rank,
        'candidate_parent_rule': 'B(c)=phi(1,phi(1,omega^(v3(bits3(c))))), c=V+suffix_after_P1',
        'term_rule': 'B(c_n), omega^(1+B(c_n)), succ(B(c_n)) for plain, L1, Z endings',
        'counts': dict(counts),
        'adjacent_order': {
            'valued_parent_count': len(parents),
            'inversion_count': len(inversions),
            'shortest_inversions': inversions[:20],
        },
        'examples': {
            'unknown': sorted(unknown_examples,
                              key=lambda x: (len(x['raw']), x['raw']))[:20],
            'term_not_below_parent': sorted(term_above_examples,
                                            key=lambda x: (len(x['raw']), x['raw'], x['term_n']))[:20],
            'sup3_differs': sorted(sup3_diff_examples,
                                   key=lambda x: (len(x['raw']), x['raw']))[:20],
            'sup6_differs': sorted(sup6_diff_examples,
                                   key=lambda x: (len(x['raw']), x['raw']))[:20],
            'term_parse_or_value_issues': sorted(term_issue_examples,
                                                 key=lambda x: (len(x['raw']), x['raw'], x['term_n']))[:20],
        },
        'rows': rows,
        'elapsed_seconds': round(time.monotonic() - start, 3),
    }
    out_path.write_text(json.dumps(report, ensure_ascii=False,
                                   separators=(',', ':')) + '\n')
    print('counts', dict(counts))
    print('adjacent valued parents', len(parents), 'inversions', len(inversions))
    for key, values in report['examples'].items():
        print(key, values[:5])
    print('saved', out_path, out_path.stat().st_size, 'bytes; elapsed',
          report['elapsed_seconds'])


if __name__ == '__main__':
    main()
