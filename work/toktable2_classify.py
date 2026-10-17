"""Classify all legacy-table disagreements, preserving real-term evidence."""
import collections
import csv
import json
from pathlib import Path

import harness
import token_value as V
from ordinal import cmp
from token_targets import pretty

HERE = Path(__file__).resolve().parent


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, list) else value


def main():
    source = json.loads((HERE / 'toktable2-comparison.json').read_text())
    rows = []
    counts = collections.Counter()
    patterns = collections.Counter()
    for reference in source['rows']:
        if reference['status'] != 'differ':
            continue
        s = tuple(map(int, reference['sequence']))
        old, new = freeze(reference['old']), freeze(reference['new'])
        tokens = V.parse_tail(s[4:])
        if tokens[:2] == ('W', 'A2'):
            family = 'W A2 descendants'
        elif tokens[:4] == ('W', 'A1', 'W', 'W'):
            family = 'W A1 W W descendants'
        elif tokens in [('W', 'E1', 'A1', 'W', 'W'),
                        ('W', 'E1', 'A2', 'W', 'W')]:
            family = 'W E1 A_k W W'
        else:
            raise AssertionError(tokens)
        repeated_w = any(a == b == 'W' for a, b in zip(tokens, tokens[1:]))
        epsilon_w = any(a.startswith('E') and b == 'W'
                        for a, b in zip(tokens, tokens[1:]))
        ak_ww = [int(tokens[i][1:]) for i in range(len(tokens) - 2)
                 if tokens[i].startswith('A') and tokens[i+1:i+3] == ('W', 'W')]
        terms = []
        for n in range(1, 6):
            term = harness.fs(s, n)
            value = V.value(term)
            terms.append(dict(n=n, sequence=''.join(map(str, term)), ordinal=value,
                              rendered=pretty(value), compare_old=cmp(value, old),
                              compare_new=cmp(value, new)))
        direction = 'new > old' if cmp(new, old) > 0 else 'new < old'
        counts[family] += 1
        patterns['has W W' if repeated_w else 'no W W'] += 1
        patterns['new > old' if cmp(new, old) > 0 else 'new < old'] += 1
        patterns['has E W' if epsilon_w else 'no E W'] += 1
        patterns['some real term >= old' if any(t['compare_old'] >= 0 for t in terms)
                 else 'five real terms below old'] += 1
        rows.append(dict(sequence=reference['sequence'], tokens=tokens,
                         region=reference['region'], family=family, direction=direction,
                         has_W_W=repeated_w, has_E_W=epsilon_w, A_k_W_W_depths=ak_ww,
                         old=old, new=new, old_rendered=pretty(old), new_rendered=pretty(new),
                         old_adjacent_violation=False, terms=terms,
                         all_terms_below_new=all(t['compare_new'] < 0 for t in terms),
                         terms_increasing=all(cmp(a['ordinal'], b['ordinal']) < 0
                                              for a, b in zip(terms, terms[1:]))))
    assert not source['legacy_adjacent_violations']
    report = dict(families=counts, patterns=patterns,
                  region_counts=collections.Counter(r['region'] for r in rows),
                  old_table_adjacent_violations=source['legacy_adjacent_violations'],
                  outside_mismatches=[], rows=rows)
    (HERE / 'toktable2-classification.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    with (HERE / 'toktable2-classification.tsv').open('w') as stream:
        writer = csv.writer(stream, delimiter='\t')
        writer.writerow(['sequence', 'canonical tokens', 'region', 'family', 'direction',
                         'W W', 'E W', 'A_k W W depths', 'old order violation', 'old', 'new',
                         'real terms n<=5 >=old'])
        for r in rows:
            writer.writerow([r['sequence'], ' '.join(r['tokens']), r['region'], r['family'],
                             r['direction'], r['has_W_W'], r['has_E_W'], r['A_k_W_W_depths'],
                             r['old_adjacent_violation'], r['old_rendered'], r['new_rendered'],
                             ','.join(str(t['n']) for t in r['terms'] if t['compare_old'] >= 0)])
    print(json.dumps({key: report[key] for key in ['families', 'patterns', 'region_counts']}, ensure_ascii=False))
    print('all local order pass', all(r['all_terms_below_new'] and r['terms_increasing'] for r in rows))
    for family in counts:
        r = next(row for row in rows if row['family'] == family)
        print(r['sequence'], ' '.join(r['tokens']), r['old_rendered'], '->', r['new_rendered'])
        for term in r['terms']:
            print(term['n'], term['rendered'], 'compare old', term['compare_old'])


if __name__ == '__main__':
    main()
