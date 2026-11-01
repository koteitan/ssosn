"""Recheck the 65 four-term sup cases through ten real terms.

Run: timeout 120 python3 work/p1_value_follow43.py
"""
from collections import Counter
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import evalord
import harness
from ordinal import lt, show
import token_value
from p1_tokens43 import P, parse_all, token_map, normalize_tokens


def main():
    data = json.loads((HERE / 'p1-tokens43-18.json').read_text())
    tm = token_map(18)
    tm['Z'] = (0,)
    for k in range(1, 18):
        tm[f'L{k}'] = (0,) + (1,)*k
    memo = {}
    reasons = {}
    unknown_tails = {}
    def value(raw):
        raw = tuple(raw)
        if raw not in memo:
            try:
                memo[raw] = token_value.value(raw)
            except token_value.Unknown as error:
                memo[raw] = None
                arg = error.args[0] if error.args else 'unknown'
                reasons[raw] = arg[0] if isinstance(arg, tuple) else str(arg)
                if isinstance(arg, tuple) and len(arg) > 1 and isinstance(arg[1], tuple):
                    unknown_tails[raw] = arg[1]
        return memo[raw]
    counts = Counter()
    cases = []
    unknowns = []
    for digits in sorted(data['standard_raw'], key=lambda x: (len(x), x)):
        raw = tuple(map(int, digits))
        parent = value(raw)
        tokens = next(iter({normalize_tokens(form) for form in
                            parse_all(raw[len(P):], tm, cap=10000)}))
        if parent is None:
            counts['parent_unknown'] += 1
            reason = reasons.get(raw, 'unknown')
            counts['unknown_'+reason] += 1
            stop_tail = unknown_tails.get(raw)
            stop_tokens = None
            if stop_tail is not None:
                parses = parse_all(stop_tail, tm, cap=10000)
                if parses:
                    stop_tokens = next(iter({normalize_tokens(form) for form in parses}))
                    counts['stop_'+'_'.join(stop_tokens[:2])] += 1
            if len(unknowns) < 50:
                unknowns.append({'raw': digits, 'tokens': list(tokens),
                                 'reason': reason,
                                 'stop_tokens': None if stop_tokens is None else list(stop_tokens)})
            continue
        if raw[-1] == 0:
            continue
        xs4 = [value(harness.fs(raw, n)) for n in range(1, 5)]
        if any(x is None for x in xs4):
            continue
        sup3, sup4 = evalord.sup(xs4[:3]), evalord.sup(xs4)
        if sup3 is not None and sup4 == sup3 == parent:
            continue
        counts['recheck_cases'] += 1
        xs = [value(harness.fs(raw, n)) for n in range(1, 11)]
        decided = 0
        for x in xs:
            if x is None:
                break
            decided += 1
        counts['recheck_terms_decided_'+str(decided)] += 1
        if any(x is not None and not lt(x, parent) for x in xs):
            counts['concrete_term_violation'] += 1
        sups = [evalord.sup(xs[:n]) if all(x is not None for x in xs[:n])
                else None for n in range(3, 11)]
        first_parent = next((n for n, x in zip(range(3, 11), sups)
                             if x == parent), None)
        if first_parent is not None:
            counts['sample_reaches_parent'] += 1
        elif decided < 10:
            counts['still_term_unknown'] += 1
        elif sups[-1] is None:
            counts['still_sup_undecided'] += 1
        else:
            counts['still_sample_different'] += 1
        cases.append({'raw': digits, 'tokens': list(tokens),
                      'terms_decided': decided, 'first_parent_sample_n': first_parent,
                      'parent': show(parent),
                      'sup_at_4': None if sup4 is None else show(sup4),
                      'sup_at_10': None if sups[-1] is None else show(sups[-1]),
                      'term_not_below': [n for n, x in enumerate(xs, 1)
                                         if x is not None and not lt(x, parent)]})
    report = {'maxlen': data['maxlen'], 'max_terms': 10,
              'counts': dict(counts), 'recheck_cases': cases,
              'shortest_unknowns': unknowns}
    path = HERE / 'p1-value-follow43.json'
    path.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    print('counts', dict(counts))
    print('shortest_unsettled', [row for row in cases
          if row['first_parent_sample_n'] is None][:8])
    print('shortest_unknowns', unknowns[:8])


if __name__ == '__main__':
    main()
