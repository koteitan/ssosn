"""Write a token table for limit standards in [P1,P2), raw length <=14.

Run: timeout 300 python3 work/p2_table44.py
"""
import json
from pathlib import Path

import harness
import p1_tokens43 as p1

HERE = Path(__file__).resolve().parent
P1 = (0, 0, 2, 1, 0, 2, 1)
DATA = HERE / 'p2-tokens44-18.json'
OUT = HERE / 'p2-table44.txt'
MAXLEN = 14


def raw_text(raw):
    return ''.join(map(str, raw))


def show_tail(raw, token_map):
    raw = tuple(raw)
    if raw[:len(P1)] != P1:
        return raw_text(raw)
    suffix = raw[len(P1):]
    forms = p1.parse_all(suffix, token_map, cap=10000)
    normalized = {p1.normalize_tokens(form) for form in forms}
    if len(normalized) != 1:
        return raw_text(raw)
    tokens = next(iter(normalized))
    return ' '.join(tokens) if tokens else '-'


def main():
    data = json.loads(DATA.read_text())
    token_map = p1.token_map(MAXLEN)
    token_map['Z'] = (0,)
    for k in range(1, MAXLEN + 1):
        token_map[f'L{k}'] = (0,) + (1,) * k

    words = sorted((tuple(map(int, spelling))
                    for spelling in data['standard_raw']
                    if len(spelling) <= MAXLEN and spelling[-1] != '0'),
                   key=raw_text)
    lines = [
        f'[P1,P2) limit standards, raw length <= {MAXLEN}',
        'token notation: Z=(0), Lk=(0,1^k), Ak=(0,1,2,(0,2)^k), '
        'W=(0,1,2,1), D=(0,2), V=(0,2,1); E normalized as A0 V',
        'raw | tokens after P1 | br | cut | term1 tail | term2 tail | term3 tail',
    ]
    for raw in words:
        seq = harness.Seq(raw, 'new')
        tails = [show_tail(harness.fs(raw, n), token_map) for n in (1, 2, 3)]
        lines.append(' | '.join((raw_text(raw), show_tail(raw, token_map),
                                 str(seq.br()), str(seq.cut()), *tails)))
    OUT.write_text('\n'.join(lines) + '\n')
    print(f'wrote {OUT}: {len(words)} limit rows, {OUT.stat().st_size} bytes')


if __name__ == '__main__':
    main()
