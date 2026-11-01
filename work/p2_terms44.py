"""Measure terms and candidate values in [P1,P2) through raw length 14.

Run: timeout 600 python3 work/p2_terms44.py
"""
from collections import Counter
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import evalord
import harness
import p1_tokens43 as p1
import token_value
import v_bits43
from ordinal import show, succ

P = (0, 0, 2, 1, 0, 2, 1)
P2 = P + (1,)
MAXLEN = 14
DATA = HERE / 'p2-tokens44-18.json'
OUT = HERE / 'p2-terms44.json'


def ord_value(raw):
    """Keep values at or above P1 explicitly unknown, as requested."""
    raw = tuple(raw)
    if raw >= P:
        return None, 'at_or_above_P1'
    try:
        return token_value.value(raw), None
    except token_value.Unknown as exc:
        return None, str(exc)
    except Exception as exc:
        return None, f'{type(exc).__name__}: {exc}'


def tokenization(raw, token_map):
    suffix = tuple(raw[len(P):])
    parses = p1.parse_all(suffix, token_map, cap=10000)
    normalized = sorted({p1.normalize_tokens(form) for form in parses})
    if len(normalized) == 1:
        return list(normalized[0]), len(parses), True
    return [], len(parses), False


def eval_sup(values):
    if any(value is None for value in values):
        return None
    result = evalord.sup(values)
    return None if result is None else show(result)


def p1_root_terms():
    """Print the actual P1[n] copies and their v2 ranks, n=1..6."""
    base = (0, 0, 2, 1)
    token_map = p1.token_map(18)
    rows = []
    for n in range(1, 7):
        copies = ('D',) + ('V', 'D') * (n - 1)
        raw_term = base + sum((token_map[t] for t in copies), ()) + (0,)
        actual = tuple(harness.fs(P, n))
        if raw_term != actual:
            raise AssertionError((n, raw_term, actual))
        rank = v_bits43.rank(copies)
        term_value, reason = ord_value(actual)
        rows.append({
            'n': n,
            'copy_tokens': list(copies),
            'copy_bits': ''.join(map(str, v_bits43.bits(copies))),
            'v2': show(rank),
            'raw_term': ''.join(map(str, actual)),
            'token_value': None if term_value is None else show(term_value),
            'token_value_reason': reason,
        })
    return rows


def main():
    started = time.monotonic()
    token_value.P1_ROOT_EXPERIMENT = True
    token_value.P1_V_FOLD_EXPERIMENT = False
    token_value.P1_V_BITS_EXPERIMENT = True
    token_value.P1_V_RAW_EXPERIMENT = False
    token_value.BOUNDARY_EXPERIMENT = False

    data = json.loads(DATA.read_text())
    token_map = p1.token_map(18)
    rows = []
    counts = Counter()
    for spelling in data['standard_raw']:
        raw = tuple(map(int, spelling))
        if len(raw) > MAXLEN:
            continue
        assert raw[:len(P)] == P and raw < P2
        cut = harness.Seq(raw, 'new').cut()
        tokens, parse_count, parse_unique = tokenization(raw, token_map)
        row = {
            'raw': spelling,
            'tokens': tokens,
            'token_parse_count': parse_count,
            'token_parse_unique': parse_unique,
            'cut': cut,
            'kind': 'successor' if raw[-1] == 0 else 'limit',
            'term_values': [],
            'sup': None,
            'value': None,
            'status': None,
        }
        if raw[-1] == 0:
            parent = raw[:-1]
            parent_value, reason = ord_value(parent)
            if parent_value is None:
                row['status'] = 'unknown_parent'
                row['reason'] = reason
                counts['successor_unknown'] += 1
            else:
                row['value'] = show(succ(parent_value))
                row['parent_value'] = show(parent_value)
                row['status'] = 'decided_successor'
                counts['successor_decided'] += 1
        else:
            terms = []
            for n in range(1, 9):
                term = tuple(harness.fs(raw, n))
                term_value, reason = ord_value(term)
                terms.append(term_value)
                row['term_values'].append({
                    'n': n,
                    'raw': ''.join(map(str, term)),
                    'value': None if term_value is None else show(term_value),
                    'reason': reason,
                })
            row['all_8_terms_decided'] = all(value is not None for value in terms)
            counts['limit_words'] += 1
            counts['limit_terms_decided'] += sum(value is not None for value in terms)
            if row['all_8_terms_decided']:
                sup3 = eval_sup(terms[:3])
                sup6 = eval_sup(terms[:6])
                sup8 = eval_sup(terms)
                row['sup'] = {'3': sup3, '6': sup6, '8': sup8}
                if sup3 is not None and sup3 == sup6 == sup8:
                    row['value'] = sup8
                    row['status'] = 'decided_limit'
                    counts['limit_decided'] += 1
                else:
                    row['status'] = 'sup_undecided_or_disagrees'
                    counts['limit_sup_undecided'] += 1
            else:
                row['status'] = 'unknown_term'
                counts['limit_unknown_term'] += 1
        counts['total'] += 1
        if row['value'] is not None:
            counts['decided'] += 1
        else:
            counts['undecided'] += 1
        rows.append(row)

    roots = p1_root_terms()
    decided = sorted((r for r in rows if r['value'] is not None),
                     key=lambda r: (r['raw'], r['value']))
    # Sort by ordinal value, not by the display string.
    # `value` for limit rows is the agreed sampled sup; parse it from the stored
    # first eight terms so sorting uses ordinal structure rather than text.
    def ordinal_for(row):
        if row['kind'] == 'successor':
            parent, _ = ord_value(tuple(map(int, row['raw'][:-1])))
            return None if parent is None else succ(parent)
        term_values = [ord_value(tuple(map(int, t['raw'])))[0]
                       for t in row['term_values']]
        return evalord.sup(term_values[:3]) if all(v is not None for v in term_values) else None
    valued = [(ordinal_for(row), row) for row in decided]
    valued = [(value, row) for value, row in valued if value is not None]
    valued.sort(key=lambda pair: pair[0])
    smallest = [{'raw': row['raw'], 'value': row['value']} for _, row in valued[:30]]

    report = {
        'range': '[P1,P2)', 'max_raw_length': MAXLEN,
        'flags': {'P1_ROOT_EXPERIMENT': True,
                  'P1_V_BITS_EXPERIMENT': True},
        'counts': dict(counts),
        'p1_root_terms': roots,
        'smallest_30': smallest,
        'rows': rows,
        'elapsed_seconds': round(time.monotonic() - started, 3),
    }
    OUT.write_text(json.dumps(report, ensure_ascii=False,
                              separators=(',', ':')) + '\n')
    print('counts', dict(counts))
    print('P1 root terms n=1..6')
    for row in roots:
        print(row['n'], ''.join(row['copy_tokens']), row['copy_bits'],
              row['v2'], row['raw_term'], row['token_value'])
    print('smallest 30 (ordinal order)')
    for row in smallest:
        print(row['raw'], row['value'])
    print('saved', OUT, 'bytes', OUT.stat().st_size,
          'elapsed', report['elapsed_seconds'])


if __name__ == '__main__':
    main()
