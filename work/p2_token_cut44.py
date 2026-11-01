"""Apply the §43 token-only cut predictions to [P1,P2), length <= 18.

Run: timeout 600 python3 work/p2_token_cut44.py
"""
from collections import Counter, defaultdict
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import harness
import p1_token_cut43 as cut43
import p1_tokens43 as p1

P1 = (0, 0, 2, 1, 0, 2, 1)
DATA = HERE / 'p2-tokens44-18.json'
OUT = HERE / 'p2-token-cut44.json'
MAXLEN = 18

# Reuse the token-only formulas while translating their origin to the new root.
cut43.P = P1


def last_kind(tokens):
    if not tokens:
        return 'ROOT'
    token = tokens[-1]
    if token == 'Z':
        return 'Z'
    if token.startswith('L'):
        return 'L'
    if token.startswith('A'):
        return 'A'
    return token


def predicted_br(tokens, raw):
    if not tokens:
        return 2
    if tokens[-1].startswith('A') and tokens[-1] != 'A0':
        return 3
    if raw[-1] == 2 and tokens[-1] == 'D':
        previous = next((t for t in reversed(tokens[:-1]) if t not in ('D', 'V')), None)
        return 3 if previous == 'W' else 2
    return 2


def predict(raw, tokens, raw_map, br):
    """Return (cut prediction, rule label), or (None, reason)."""
    if not tokens:
        return 2, 'root'
    last = tokens[-1]
    if last == 'Z':
        # For a successor, mbp(x)=L throughout because no entry is < 0.
        return len(raw), 'terminal_Z'
    if last.startswith('L'):
        _, value = cut43.lower_cut(raw, tokens, raw_map)
        return value, 'lower_L'
    if last == 'V':
        return cut43.v_run_cut(tokens, raw_map, root_v=True), 'terminal_V_run'
    if last == 'W':
        _, value = cut43.w_cut(tokens, raw_map)
        return value, 'final_W'
    if last == 'D':
        if br == 3:
            _, _, value = cut43.third_parent_cut(raw, tokens, raw_map)
            return value, 'br3'
        _, value = cut43.d_cut(tokens, raw_map)
        return value, 'final_D_br2'
    if last.startswith('A'):
        if br == 3:
            _, _, value = cut43.third_parent_cut(raw, tokens, raw_map)
            return value, 'br3'
        if last == 'A0':
            return cut43.heads(tokens, raw_map)[-1][1] + 1, 'final_A0'
        return None, 'unexpected_A_br2'
    return None, f'unsupported_{last}'


def text(raw):
    return ''.join(map(str, raw))


def main():
    data = json.loads(DATA.read_text())
    raw_map = p1.token_map(MAXLEN)
    raw_map['Z'] = (0,)
    for k in range(1, MAXLEN + 1):
        raw_map[f'L{k}'] = (0,) + (1,) * k

    summary = Counter()
    groups = defaultdict(Counter)
    mismatch_examples = defaultdict(list)
    root_positions = Counter()
    predicted_root_positions = Counter()
    root_cut_kinds = Counter()
    rows = []

    for spelling in data['standard_raw']:
        raw = tuple(map(int, spelling))
        if len(raw) > MAXLEN:
            continue
        forms = p1.parse_all(raw[len(P1):], raw_map, cap=10000)
        normalized = sorted({p1.normalize_tokens(form) for form in forms})
        if not forms:
            parse_status = 'none'
            tokens = None
            kind = 'UNPARSED'
        elif len(normalized) == 1:
            parse_status = 'unique'
            tokens = normalized[0]
            kind = last_kind(tokens)
        else:
            parse_status = 'ambiguous'
            tokens = None
            kinds = {last_kind(form) for form in normalized}
            kind = next(iter(kinds)) if len(kinds) == 1 else 'AMBIG'

        seq = harness.Seq(raw, 'new')
        actual_br = seq.br()
        actual_cut = seq.cut()
        summary[f'parse_{parse_status}'] += 1
        summary['total'] += 1
        group_key = (kind, actual_br)
        group = groups[group_key]
        group['total'] += 1
        group[f'parse_{parse_status}'] += 1

        pred = None
        rule = None
        br_pred = None
        if tokens is not None:
            br_pred = predicted_br(tokens, raw)
            pred, rule = predict(raw, tokens, raw_map, br_pred)
            summary['unique_with_prediction' if pred is not None else 'unique_no_prediction'] += 1
            group['unique'] += 1
            group['br_prediction_match' if br_pred == actual_br else 'br_prediction_differ'] += 1
            if pred is None:
                group['no_cut_prediction'] += 1
            elif pred == actual_cut:
                group['cut_match'] += 1
            else:
                group['cut_differ'] += 1
                item = {
                    'raw': spelling,
                    'tokens': list(tokens),
                    'br': actual_br,
                    'predicted_cut': pred,
                    'actual_cut': actual_cut,
                    'term1': text(harness.fs(raw, 1)),
                    'term2': text(harness.fs(raw, 2)),
                    'rule': rule,
                }
                mismatch_examples[group_key].append(item)
        else:
            group['no_unique_tokenization'] += 1

        if actual_cut <= 7:
            summary['actual_cut_within_root_0_to_7'] += 1
            root_positions[str(actual_cut)] += 1
            root_cut_kinds[(kind, actual_br, actual_cut)] += 1
        else:
            summary['actual_cut_after_root'] += 1
        if pred is not None and pred <= 7:
            summary['predicted_cut_within_root_0_to_7'] += 1
            predicted_root_positions[str(pred)] += 1

        rows.append({
            'raw': spelling,
            'tokens': None if tokens is None else list(tokens),
            'parse_status': parse_status,
            'last_kind': kind,
            'br': actual_br,
            'predicted_br': br_pred,
            'predicted_cut': pred,
            'actual_cut': actual_cut,
            'rule': rule,
        })

    report_groups = []
    for (kind, br), counts in sorted(groups.items()):
        examples = sorted(mismatch_examples[(kind, br)],
                          key=lambda x: (len(x['raw']), x['raw']))[:3]
        report_groups.append({
            'last_kind': kind,
            'br': br,
            'counts': dict(counts),
            'shortest_cut_mismatches': examples,
        })

    report = {
        'range': '[P1,P2)', 'max_raw_length': MAXLEN,
        'token_map': 'Z,L_k,A_k,W,D,V; E normalized as A0,V',
        'root_cut_threshold': 7,
        'summary': dict(summary),
        'actual_root_cut_positions': dict(root_positions),
        'predicted_root_cut_positions': dict(predicted_root_positions),
        'actual_root_cut_by_kind': [
            {'last_kind': k, 'br': br, 'cut': pos, 'count': count}
            for (k, br, pos), count in sorted(root_cut_kinds.items())
        ],
        'groups': report_groups,
        'rows': rows,
    }
    OUT.write_text(json.dumps(report, ensure_ascii=False,
                              separators=(',', ':')) + '\n')
    print('summary', dict(summary))
    print('actual root cut positions', dict(root_positions))
    print('predicted root cut positions', dict(predicted_root_positions))
    print('groups')
    for row in report_groups:
        print(row['last_kind'], row['br'], row['counts'],
              'mismatches', row['shortest_cut_mismatches'])
    print('saved', OUT, OUT.stat().st_size, 'bytes')


if __name__ == '__main__':
    main()
