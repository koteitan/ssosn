"""Measure an existing ordinal candidate on standard words in [P,P1).

Candidate: decode the canonical token word and apply token_value.value to the
resulting (0,0)-block decomposition. This is the old, conjectural evaluator,
not a new value theorem. Every unknown stays unknown.

Run: timeout 120 python3 work/p1_value43.py
"""
from collections import Counter
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import evalord
import harness
from ordinal import ONE, add, lt, nat, show, succ, w
import token_value
from p1_tokens43 import P, parse_all, token_map, normalize_tokens


def main():
    here = Path(__file__).resolve().parent
    data = json.loads((here / 'p1-tokens43-18.json').read_text())
    tm = token_map(18)
    tm['Z'] = (0,)
    for k in range(1, 18):
        tm[f'L{k}'] = (0,) + (1,)*k
    memo = {}
    def candidate(raw):
        raw = tuple(raw)
        if raw not in memo:
            try:
                memo[raw] = token_value.value(raw)
            except token_value.Unknown:
                memo[raw] = None
        return memo[raw]
    beta = candidate(P)
    assert beta is not None
    def lower_family(tokens):
        """Closed candidate for Z^m L_k Z^r, derived from its real blocks."""
        m = 0
        while m < len(tokens) and tokens[m] == 'Z':
            m += 1
        if m == len(tokens) or not tokens[m].startswith('L'):
            return None
        k = int(tokens[m][1:])
        trailing = tokens[m+1:]
        if any(t != 'Z' for t in trailing):
            return None
        value = succ(beta) if m == 0 else ONE
        for _ in range(k):
            value = w(value)
        if m:
            value = add(beta, value)
        return add(value, nat(len(trailing)))
    counts = Counter()
    failures = []
    for digits in data['standard_raw']:
        raw = tuple(map(int, digits))
        tokens = next(iter({normalize_tokens(form) for form in
                            parse_all(raw[len(P):], tm, cap=10000)}))
        assert P + sum((tm[t] for t in tokens), ()) == raw
        value = candidate(raw)
        closed = lower_family(tokens)
        if closed is not None:
            counts['closed_lower_family'] += 1
            if value is None:
                counts['closed_lower_old_unknown'] += 1
            elif closed == value:
                counts['closed_lower_old_agree'] += 1
            else:
                counts['closed_lower_old_differ'] += 1
                failures.append({'raw': digits, 'kind': 'closed_lower_differ',
                                 'closed': show(closed), 'old': show(value)})
        if value is None:
            counts['parent_unknown'] += 1
            continue
        counts['parent_decided'] += 1
        if raw[-1] == 0:
            parent = candidate(raw[:-1])
            if parent is None:
                counts['successor_parent_unknown'] += 1
            elif value == succ(parent):
                counts['successor_agree'] += 1
            else:
                counts['successor_differ'] += 1
                failures.append({'raw': digits, 'kind': 'successor',
                                 'actual': show(value), 'expected': show(succ(parent))})
            continue
        terms = [candidate(harness.fs(raw, n)) for n in range(1, 5)]
        if any(x is None for x in terms):
            counts['limit_term_unknown'] += 1
            continue
        counts['limit_all_four_terms'] += 1
        if not all(lt(x, value) for x in terms):
            counts['limit_term_not_below'] += 1
            failures.append({'raw': digits, 'kind': 'term_not_below',
                             'parent': show(value),
                             'terms': [show(x) for x in terms]})
        sup3 = evalord.sup(terms[:3])
        sup4 = evalord.sup(terms)
        if sup3 is None or sup4 is None or sup3 != sup4:
            counts['limit_sup_undecided'] += 1
        elif sup4 == value:
            counts['limit_sup_agree'] += 1
        else:
            counts['limit_sup_differ'] += 1
            failures.append({'raw': digits, 'kind': 'sup_differ',
                             'parent': show(value), 'sup': show(sup4),
                             'terms': [show(x) for x in terms]})
    report = {'maxlen': data['maxlen'], 'candidate': 'token_value.value via raw(canonical tokens)',
              'counts': dict(counts), 'failures': failures[:100],
              'failure_count': len(failures)}
    path = here / 'p1-value43.json'
    path.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    print('counts', dict(counts), 'failures', len(failures),
          'first', failures[:3])


if __name__ == '__main__':
    main()
