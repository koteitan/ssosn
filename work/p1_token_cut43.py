"""Token-position cut rules in [P,P1), checked against Seq.cut.

Run after p1_tokens43.py: timeout 60 python3 work/p1_token_cut43.py
The predictors below never call Seq.sp, Seq.br, Seq.mbp, or Seq.cut.
"""
from collections import Counter
import json
from pathlib import Path

import harness
from p1_tokens43 import P, parse_all, token_map, normalize_tokens


def heads(tokens, raw_map):
    position = len(P) + 1  # one-based
    out = []
    for token in tokens:
        out.append((token, position))
        position += len(raw_map[token])
    return out


def comparison_tokens(tokens):
    """Use E_k=A_k V only for lexical comparisons across token boundaries."""
    out = []
    i = 0
    while i < len(tokens):
        if tokens[i].startswith('A') and i+1 < len(tokens) and tokens[i+1] == 'V':
            out.append('E'+tokens[i][1:])
            i += 2
        else:
            out.append(tokens[i])
            i += 1
    return tuple(out)


def token_rank(token):
    if token == 'Z': return 0
    if token.startswith('L'): return 100+int(token[1:])
    if token.startswith('A'): return 1000+int(token[1:])
    if token.startswith('E'): return 2000-int(token[1:])
    return {'W': 3000, 'D': 4000, 'V': 5000}[token]


def lexical_key(tokens):
    return tuple(token_rank(token) for token in comparison_tokens(tokens))


def lower_cut(raw, tokens, raw_map):
    """Pure token rule for a final L_k."""
    k = int(tokens[-1][1:])
    positions = heads(tokens, raw_map)
    p2 = 1
    for token, position in positions[:-1]:
        if token == 'Z' or token.startswith('L') and int(token[1:]) < k:
            p2 = position
    if p2 == 1:
        return p2, 2
    candidates = []
    for index, (token, position) in enumerate(positions):
        if position < p2:
            continue
        remainder = lexical_key(tokens[index+1:])
        if token == 'V':
            key = (3, 0, remainder)
        elif token == 'D':
            key = (2, 0, remainder)
        elif token.startswith('L'):
            key = (1, int(token[1:]), remainder)
        else:
            continue
        candidates.append((key, position))
    return p2, max(candidates)[1]


def br3_from_tokens(tokens):
    if tokens[-1].startswith('A') and tokens[-1] != 'A0':
        return True
    if tokens[-1] != 'D':
        return False
    return next((t for t in reversed(tokens[:-1]) if t not in ('D', 'V')), None) == 'W'


def third_parent_cut(raw, tokens, raw_map):
    """Token heads for p3, then the only winning token positions seen at br=3."""
    positions = heads(tokens, raw_map)
    if tokens[-1].startswith('A'):
        p2 = positions[-1][1]
    else:
        p2 = next(position for token, position in reversed(positions)
                  if token == 'W')
    target_index = next(i for i, (_, position) in enumerate(positions)
                        if position == p2)
    target = lexical_key(tokens[target_index:])
    p3 = 1
    for index, (token, position) in enumerate(positions):
        if index >= target_index:
            break
        if lexical_key(tokens[index:]) < target:
            p3 = position
    if p3 == 1:
        return p2, p3, 2
    candidates = []
    for index, (token, position) in enumerate(positions):
        if token in ('D', 'V') and position >= p3:
            candidates.append(((2 if token == 'V' else 1,
                                lexical_key(tokens[index+1:])), position))
        if token == 'W' and position+1 >= p3:
            candidates.append(((2, lexical_key(tokens[index+1:])), position+1))
    return p2, p3, max(candidates)[1]


def w_cut(tokens, raw_map):
    p2 = 1
    positions = heads(tokens, raw_map)
    for token, position in positions[:-1]:
        if token == 'Z' or token.startswith(('L', 'A')):
            p2 = position
    if p2 == 1:
        return p2, 2
    candidates = []
    for index, (token, position) in enumerate(positions):
        tail = tokens[index+1:]
        if position >= p2 and token == 'V':
            candidates.append(((3, lexical_key(tail)), position))
        if position >= p2 and token == 'W':
            candidates.append(((1, lexical_key(tail)), position))
        if token.startswith('A'):
            depth = int(token[1:])
            for m in range(depth):
                candidate = position+3+2*m
                if candidate >= p2:
                    remainder = ('D',)*(depth-m-1)+tail
                    candidates.append(((2, lexical_key(remainder)), candidate))
    return p2, max(candidates)[1]


def d_cut(tokens, raw_map):
    p2 = 1
    positions = heads(tokens, raw_map)
    for token, position in positions[:-1]:
        if token in ('Z', 'W') or token.startswith(('L', 'A')):
            p2 = position
    if p2 == 1:
        return p2, 2
    candidates = []
    for index, (token, position) in enumerate(positions):
        if position >= p2 and token in ('D', 'V'):
            candidates.append(((2 if token == 'V' else 1,
                                lexical_key(tokens[index+1:])), position))
    return p2, max(candidates)[1]


def v_run_cut(tokens, raw_map, root_v=False):
    """Cut after a terminal V-run's first head, with an optional root join.

    If the whole token tail is V^m and the base already ends in V, the run
    crosses the base boundary and the cut is the outer root cut at 2.
    """
    m = 0
    while m < len(tokens) and tokens[-1-m] == 'V':
        m += 1
    if not m:
        raise ValueError(('no trailing V run', tokens))
    if root_v and m == len(tokens):
        return 2
    positions = heads(tokens, raw_map)
    if m >= 2:
        return positions[len(tokens)-m][1]
    return positions[-1][1]


def main():
    here = Path(__file__).resolve().parent
    data = json.loads((here / 'p1-tokens43-18.json').read_text())
    tm = token_map(18)
    tm['Z'] = (0,)
    for k in range(1, 18):
        tm[f'L{k}'] = (0,) + (1,)*k
    counts = Counter()
    failures = []
    examples = []
    suffix_words = set()
    for digits in data['standard_raw']:
        raw = tuple(map(int, digits))
        forms = parse_all(raw[len(P):], tm, cap=10000)
        tokens = next(iter({normalize_tokens(form) for form in forms}))
        for offset in range(len(tokens)+1):
            suffix_words.add(tokens[offset:])
        if raw[-1] == 0:
            continue
        if not tokens:
            assert raw == P and harness.Seq(raw, 'new').br() == 2
            assert harness.Seq(raw, 'new').cut() == 2
            assert all(harness.fs(raw, n) == raw[:2] +
                       (raw[2:-1] + (raw[-1]-1,))*n for n in range(1, 6))
            counts['base_P_br2'] += 1
            counts['predicted_cut'] += 1
            continue
        seq = harness.Seq(raw, 'new')
        actual = seq.cut()
        br = seq.br()
        if raw[-1] == 1:
            counts['terminal_1'] += 1
            expected_head = len(raw)-len(tm[tokens[-1]])+1
            if seq.p(1) != expected_head or br != 2:
                failures.append({'raw': digits, 'kind': 'terminal_one',
                                 'p1': seq.p(1), 'expected_head': expected_head,
                                 'br': br})
        if tokens[-1].startswith('L'):
            p2, predicted = lower_cut(raw, tokens, tm)
            counts['final_L'] += 1
            if p2 != seq.p(2) or predicted != actual or br != 2:
                failures.append({'raw': digits, 'kind': 'L', 'p2': p2,
                                 'actual_p2': seq.p(2), 'predicted': predicted,
                                 'actual': actual, 'br': br})
            if len(examples) < 8:
                examples.append({'raw': digits, 'tokens': list(tokens),
                                 'p2': p2, 'cut': predicted})
        elif tokens[-1] == 'V':
            predicted = v_run_cut(tokens, tm, root_v=False)
            counts['final_V'] += 1
            run = 0
            while run < len(tokens) and tokens[-1-run] == 'V':
                run += 1
            counts['terminal_V_run_ge_2'] += int(run >= 2)
        elif tokens[-1] == 'W':
            p2, predicted = w_cut(tokens, tm)
            counts['final_W'] += 1
            if p2 != seq.p(2):
                failures.append({'raw': digits, 'kind': 'W_p2',
                                 'predicted': p2, 'actual': seq.p(2)})
        if raw[-1] == 2:
            predicted_br3 = br3_from_tokens(tokens)
            counts['terminal_2'] += 1
            if predicted_br3 != (br == 3):
                failures.append({'raw': digits, 'kind': 'br3',
                                 'predicted': predicted_br3, 'actual': br})
            if predicted_br3:
                counts['br3'] += 1
                p2, p3, predicted = third_parent_cut(raw, tokens, tm)
                if p3 == 1:
                    p3_owner = 'root1'
                else:
                    p3_owner = next(token[0] for token, position in heads(tokens, tm)
                                    if position == p3)
                counts['p3_'+p3_owner] += 1
                if predicted == 2:
                    winner = 'root2'
                else:
                    winner = next(('W_inside' if token == 'W' and position+1 == predicted
                                   else token)
                                  for token, position in heads(tokens, tm)
                                  if position == predicted or
                                  token == 'W' and position+1 == predicted)
                counts['winner_'+winner] += 1
                if p2 != seq.p(2) or p3 != seq.p(3):
                    failures.append({'raw': digits, 'kind': 'third_parent',
                                     'p2': p2, 'p3': p3, 'predicted': predicted,
                                     'actual_p2': seq.p(2),
                                     'actual_p3': seq.p(3), 'actual': actual})
            elif tokens[-1] == 'A0':
                predicted = heads(tokens, tm)[-1][1]+1
                counts['final_A0'] += 1
            elif tokens[-1] == 'D':
                p2, predicted = d_cut(tokens, tm)
                counts['final_D_br2'] += 1
                if p2 != seq.p(2):
                    failures.append({'raw': digits, 'kind': 'D_p2',
                                     'predicted': p2, 'actual': seq.p(2)})
        counts['predicted_cut'] += 1
        if predicted != actual:
            failures.append({'raw': digits, 'kind': 'cut',
                             'predicted': predicted, 'actual': actual})
        if any(harness.fs(raw, n) != raw[:predicted] +
               (raw[predicted:-1] + (raw[-1]-1,))*n for n in range(1, 6)):
            failures.append({'raw': digits, 'kind': 'real_terms'})
    ordered_suffixes = sorted(suffix_words, key=lexical_key)
    counts['comparison_suffixes'] = len(ordered_suffixes)
    for left, right in zip(ordered_suffixes, ordered_suffixes[1:]):
        raw_left = sum((tm[t] for t in left), ())
        raw_right = sum((tm[t] for t in right), ())
        if not raw_left < raw_right:
            failures.append({'kind': 'token_order', 'left': list(left),
                             'right': list(right)})
    report = {'maxlen': data['maxlen'], 'counts': dict(counts),
              'failures': failures, 'examples': examples}
    path = here / 'p1-token-cut43.json'
    path.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    print('counts', dict(counts), 'failures', len(failures),
          'first', failures[:3])


if __name__ == '__main__':
    main()
