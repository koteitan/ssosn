"""Flagged D/W-root experiment above P; run with timeout 750.

The candidate is deliberately conjectural.  A finite sampled sup is evidence,
not a proof that the parent equals that sup.
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
from ordinal import lt, show, succ
import token_value
from p1_tokens43 import P


def digits(raw):
    return ''.join(map(str, raw))


def old_value(raw):
    try:
        return token_value.value(raw)
    except token_value.Unknown:
        return None


def candidate(raw):
    try:
        return token_value.value(raw)
    except token_value.Unknown:
        return None


def main():
    data = json.loads((HERE / 'p1-tokens43-18.json').read_text())
    words = sorted((tuple(map(int, s)) for s in data['standard_raw']),
                   key=lambda raw: (len(raw), raw))
    old = {raw: old_value(raw) for raw in words}
    token_value.P1_ROOT_EXPERIMENT = True
    token_value.value.cache_clear()
    new = {raw: candidate(raw) for raw in words}
    counts = Counter()
    issues = []
    audit_started = time.monotonic()
    for raw in words:
        prev, value = old[raw], new[raw]
        if prev is None:
            counts['old_unknown'] += 1
            counts['old_unknown_new_decided' if value is not None else
                   'old_unknown_still_unknown'] += 1
        else:
            counts['old_decided'] += 1
            if value != prev:
                counts['old_value_changed'] += 1
                issues.append({'kind': 'old_changed', 'raw': digits(raw),
                               'old': show(prev), 'new': None if value is None else show(value)})
        if value is None:
            continue
        # The earlier §43 audit already measured old-decided words.  This
        # experiment measures the newly decided cases, with a bounded run.
        if prev is not None:
            continue
        if raw[-1] == 0:
            parent = new.get(raw[:-1])
            if parent is None:
                parent = candidate(raw[:-1])
            if parent is None:
                counts['successor_parent_unknown'] += 1
            elif value == succ(parent):
                counts['successor_agree'] += 1
            else:
                counts['successor_differ'] += 1
                issues.append({'kind': 'successor', 'raw': digits(raw),
                               'parent': show(parent), 'value': show(value)})
            continue
        counts['limit_decided'] += 1
        if time.monotonic() - audit_started > 600:
            counts['limit_audit_budget_skipped'] += 1
            continue
        xs = []
        for n in range(1, 11):
            x = candidate(harness.fs(raw, n))
            xs.append(x)
            if x is None:
                break
        n_decided = sum(x is not None for x in xs)
        counts['limit_term_decided_total'] += n_decided
        counts['limit_all_10' if len(xs) == 10 and n_decided == 10 else 'limit_some_unknown'] += 1
        bad = [n for n, x in enumerate(xs, 1) if x is not None and not lt(x, value)]
        if bad:
            counts['limit_term_not_below'] += 1
            if len(issues) < 100:
                issues.append({'kind': 'term_not_below', 'raw': digits(raw),
                               'parent': show(value), 'bad_n': bad,
                               'term': show(xs[bad[0]-1])})
        if len(xs) == 10 and n_decided == 10:
            sup4, sup10 = evalord.sup(xs[:4]), evalord.sup(xs)
            if sup4 is None or sup10 is None or sup4 != sup10:
                counts['limit_sup_unstable'] += 1
            elif sup10 == value:
                counts['limit_sup_sample_agree'] += 1
            else:
                counts['limit_sup_sample_differ'] += 1
                if len(issues) < 100:
                    issues.append({'kind': 'sample_sup_differ', 'raw': digits(raw),
                                   'parent': show(value), 'sup10': show(sup10)})
    ordered = sorted((raw, value) for raw, value in new.items() if value is not None)
    order_bad = []
    for (left, x), (right, y) in zip(ordered, ordered[1:]):
        if not lt(x, y):
            counts['adjacent_order_bad'] += 1
            if len(order_bad) < 100:
                order_bad.append({'left': digits(left), 'right': digits(right),
                                  'left_value': show(x), 'right_value': show(y)})
    roots = {}
    root_tails = {'P D': (0,2), 'P V': (0,2,1), 'P W': (0,1,2,1),
                  'P D Z': (0,2,0), 'P D L1': (0,2,0,1),
                  'P D D': (0,2,0,2)}
    for name, tail in root_tails.items():
        raw = P + tail
        row = {'raw': digits(raw), 'value': None if candidate(raw) is None else show(candidate(raw))}
        if raw[-1] == 0:
            row['successor_of'] = digits(raw[:-1])
        else:
            row['cut'] = harness.Seq(raw, 'new').cut()
            row['terms'] = []
            for n in range(1, 11):
                term = harness.fs(raw, n)
                value = candidate(term)
                row['terms'].append({'n': n, 'raw': digits(term),
                                     'value': None if value is None else show(value)})
        roots[name] = row
    report = {'range': '[P,P1)', 'maxlen': 18, 'max_terms': 10,
              'candidate': 'P1_ROOT_EXPERIMENT (old first, general-copy D/W fallback)',
              'counts': dict(counts), 'issues': issues, 'order_bad': order_bad,
              'roots': roots}
    (HERE / 'p1-root-follow43.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print('counts', dict(counts))
    print('issues', issues[:5])
    print('order_bad', order_bad[:5])
    for name, row in roots.items():
        print(name, row['raw'], row['value'],
              'terms_decided', sum(x['value'] is not None for x in row.get('terms', [])))


if __name__ == '__main__':
    main()
