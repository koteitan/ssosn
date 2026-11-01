"""Predict cuts from two sp parents and a suffix maximum, without Seq.cut.

Run after p1_tokens43.py: timeout 60 python3 work/p1_parent_cut43.py
"""
from collections import Counter, defaultdict
import json
from pathlib import Path

import harness
from p1_tokens43 import P, parse_all, token_map, normalize_tokens


def predict_cut_from_p2(raw, seq):
    """For br=2: rightmost maximum suffix after an eligible entry >= p2."""
    length = len(raw)
    p1 = seq.sp(length)
    p2 = seq.sp(p1)
    candidates = [i for i in range(p2, length) if raw[i-1] < raw[-1]]
    assert candidates, (raw, p2)
    cut = max(candidates, key=lambda i: (raw[i:], i))
    return p1, p2, cut


def main():
    here = Path(__file__).resolve().parent
    data = json.loads((here / 'p1-tokens43-18.json').read_text())
    tm = token_map(18)
    tm['Z'] = (0,)
    for k in range(1, 18):
        tm[f'L{k}'] = (0,) + (1,)*k
    counts = Counter()
    examples = defaultdict(list)
    failures = []
    for digits in data['standard_raw']:
        raw = tuple(map(int, digits))
        if raw[-1] == 0:
            counts['successor_last_zero'] += 1
            continue
        seq = harness.Seq(raw, 'new')
        forms = parse_all(raw[len(P):], tm, cap=10000)
        words = next(iter({normalize_tokens(form) for form in forms}))
        last_token = words[-1] if words else 'base_P'
        p1, p2, predicted = predict_cut_from_p2(raw, seq)
        actual = seq.cut()
        br = seq.br()
        family = last_token[0] if last_token != 'base_P' else 'base'
        key = f'last_{raw[-1]}_{family}_br_{br}'
        counts[key] += 1
        if predicted == actual:
            counts['predicted_agree'] += 1
            if any(harness.fs(raw, n) != raw[:predicted] +
                   (raw[predicted:-1] + (raw[-1]-1,))*n for n in range(1, 6)):
                failures.append({'raw': digits, 'reason': 'real term mismatch'})
        else:
            counts['predicted_differ'] += 1
            failures.append({'raw': digits, 'reason': 'cut differs',
                             'p1': p1, 'p2': p2, 'predicted': predicted,
                             'actual': actual, 'br': br, 'tokens': list(words)})
        if len(examples[key]) < 4:
            examples[key].append({'raw': digits, 'tokens': list(words),
                                  'p1': p1, 'p2': p2,
                                  'predicted': predicted, 'actual': actual})
        if raw[-1] == 1:
            expected_head = len(raw)-len(tm[last_token])+1
            if p1 != expected_head or br != 2 or predicted != actual:
                failures.append({'raw': digits, 'reason': 'end-one certificate',
                                 'p1': p1, 'head': expected_head, 'br': br,
                                 'predicted': predicted, 'actual': actual})
    report = {'maxlen': data['maxlen'], 'counts': dict(counts),
              'examples': dict(examples), 'failures': failures[:100],
              'failure_count': len(failures)}
    path = here / 'p1-parent-cut43.json'
    path.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    print('counts', dict(counts), 'failures', len(failures),
          'first', failures[:3])


if __name__ == '__main__':
    main()
