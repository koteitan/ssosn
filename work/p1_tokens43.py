"""Enumerate standard forms in [P,P1) and inspect raw token parses.

Run: timeout 300 python3 work/p1_tokens43.py --maxlen 18
"""
import argparse
from collections import Counter, defaultdict
from functools import lru_cache
import gzip
import json
from pathlib import Path
import time

import harness
import std

P = (0, 0, 2, 1, 0, 2)
P1 = P + (1,)
BASE = (0, 0, 2, 1)
TOKENS = {'D': (0, 2), 'V': (0, 2, 1), 'W': (0, 1, 2, 1),
          'E': (0, 1, 2, 0, 2, 1)}


def token_map(maxlen):
    out = dict(TOKENS)
    for k in range(maxlen // 2 + 1):
        out[f'A{k}'] = (0, 1, 2) + (0, 2) * k
    return out


def parse_all(raw, token_map, cap=1000):
    @lru_cache(None)
    def go(i):
        if i == len(raw):
            return ((),)
        rows = []
        for name, unit in token_map.items():
            if raw[i:i+len(unit)] == unit:
                rows.extend((name,) + tail for tail in go(i+len(unit)))
                if len(rows) >= cap:
                    return tuple(rows[:cap])
        return tuple(rows)
    return go(0)


def token_prefix_possible(raw, token_map):
    reachable = {0}
    for i in range(len(raw) + 1):
        if i not in reachable:
            continue
        tail = raw[i:]
        if any(unit[:len(tail)] == tail for unit in token_map.values()):
            return True
        for unit in token_map.values():
            if raw[i:i+len(unit)] == unit:
                reachable.add(i+len(unit))
    return False


def normalize_tokens(tokens):
    """E is read as A0 V; merge every A_k D into A_(k+1)."""
    out = []
    for token in tokens:
        if token == 'E':
            out.extend(('A0', 'V'))
        elif token == 'D' and out and out[-1].startswith('A'):
            out[-1] = 'A' + str(int(out[-1][1:]) + 1)
        else:
            out.append(token)
    return tuple(out)


def remainder_kind(raw, token_map):
    """Longest complete token prefix; peel terminal successor zeros."""
    best = max(i for i in range(len(raw)+1) if parse_all(raw[:i], token_map))
    rem = raw[best:]
    if not rem:
        return 'complete', rem
    if all(x == 0 for x in rem):
        return 'terminal_zeros', rem
    core = rem
    while core and core[-1] == 0:
        core = core[:-1]
    if any(unit[:len(core)] == core for unit in token_map.values()):
        return 'partial_token', rem
    for j in range(1, len(core)):
        if all(x == 0 for x in core[:j]) and any(
                unit[:len(core[j:])] == core[j:] for unit in token_map.values()):
            return 'zeros_then_partial', rem
    return 'other', rem


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--maxlen', type=int, default=18)
    ap.add_argument('--out', type=Path)
    args = ap.parse_args()
    if args.maxlen < len(P):
        ap.error('maxlen is shorter than P')
    original_cut = harness.Seq.cut
    @lru_cache(maxsize=50000)
    def cached_cut(raw, mode):
        return original_cut(harness.Seq(raw, mode))
    harness.Seq.cut = lambda self: cached_cut(self.S, self.mode)
    started = time.monotonic()
    tm = token_map(args.maxlen)
    canonical_tm = {name: raw for name, raw in tm.items() if name != 'E'}
    levels = Counter(); parses = Counter(); examples = defaultdict(list)
    prefix_possible = Counter(); prefix_examples = defaultdict(list)
    remainders = Counter(); remainder_examples = defaultdict(list)
    other_digit_classes = Counter(); other_digit_examples = defaultdict(list)
    canonical = Counter(); canonical_failures = []
    final_v = {'all': 0, 'token_final': 0, 'cut_agree': 0,
               'terms_agree': 0, 'failures': [], 'examples': []}
    standard = []
    frontier = [P]
    while frontier:
        following = []
        for raw in frontier:
            if raw >= P1:
                continue
            assert std.is_standard(raw), raw
            standard.append(raw)
            levels[len(raw)] += 1
            suffix = raw[len(P):]
            forms = parse_all(suffix, tm)
            canonical_forms = parse_all(suffix, canonical_tm)
            normal_forms = {normalize_tokens(x) for x in forms}
            canonical['raw_multiple' if len(canonical_forms) > 1 else
                      'raw_unique' if canonical_forms else 'not_complete'] += 1
            if len(normal_forms) > 1:
                canonical_failures.append(''.join(map(str, raw)))
            key = 'none' if not forms else 'unique' if len(forms) == 1 else 'multiple'
            parses[key] += 1
            if len(examples[key]) < 40:
                examples[key].append({'raw': ''.join(map(str, raw)),
                                      'tokens': [list(x) for x in forms[:5]]})
            possible = token_prefix_possible(suffix, tm)
            prefix_possible['yes' if possible else 'no'] += 1
            if not possible and len(prefix_examples['no']) < 40:
                prefix_examples['no'].append(''.join(map(str, raw)))
            kind, rem = remainder_kind(suffix, canonical_tm)
            remainders[kind] += 1
            if len(remainder_examples[kind]) < 25:
                remainder_examples[kind].append({
                    'raw': ''.join(map(str, raw)),
                    'remainder': ''.join(map(str, rem))})
            if kind == 'other':
                digit_class = 'binary_01' if set(rem) <= {0, 1} else 'contains_2'
                other_digit_classes[digit_class] += 1
                if len(other_digit_examples[digit_class]) < 25:
                    other_digit_examples[digit_class].append({
                        'raw': ''.join(map(str, raw)),
                        'remainder': ''.join(map(str, rem))})
            if raw[-3:] == (0, 2, 1):
                final_v['all'] += 1
                if any(form and form[-1] == 'V' for form in forms):
                    final_v['token_final'] += 1
                cut = harness.Seq(raw, 'new').cut()
                if cut == len(raw)-2:
                    final_v['cut_agree'] += 1
                agree = all(harness.fs(raw, n) == raw[:-3] + (0, 2)*n + (0,)
                            for n in range(1, 6))
                if agree:
                    final_v['terms_agree'] += 1
                else:
                    final_v['failures'].append(''.join(map(str, raw)))
                if len(final_v['examples']) < 20:
                    final_v['examples'].append({
                        'raw': ''.join(map(str, raw)), 'cut': cut,
                        'tokens': [list(x) for x in forms[:3]],
                        'terms': [''.join(map(str, harness.fs(raw, n))) for n in range(1, 5)]})
            if len(raw) < args.maxlen:
                for digit in (0, 1, 2, 3):
                    child = raw + (digit,)
                    if child < P1 and std.is_standard(child):
                        following.append(child)
        frontier = following
        print(f'length={len(frontier[0])-1 if frontier else args.maxlen} total={len(standard)} next={len(frontier)} elapsed={time.monotonic()-started:.1f}s', flush=True)
    report = {'maxlen': args.maxlen, 'range': '[P,P1)',
              'count': len(standard), 'by_length': dict(levels),
              'parses': dict(parses), 'examples': dict(examples),
              'token_prefix_possible': dict(prefix_possible),
              'token_prefix_examples': dict(prefix_examples),
              'canonical': dict(canonical),
              'canonical_failures': canonical_failures,
              'remainders': dict(remainders),
              'remainder_examples': dict(remainder_examples),
              'other_digit_classes': dict(other_digit_classes),
              'other_digit_examples': dict(other_digit_examples),
              'final_v': final_v,
              'standard_raw': [''.join(map(str, x)) for x in standard],
              'elapsed_seconds': time.monotonic()-started}
    path = args.out or Path(__file__).with_name(f'p1-tokens43-{args.maxlen}.json')
    payload = (json.dumps(report, ensure_ascii=False, separators=(',', ':'))+'\n').encode()
    if len(payload) > 1_000_000 and path.suffix != '.gz':
        path = Path(str(path)+'.gz')
    if path.suffix == '.gz':
        with gzip.open(path, 'wb') as target:
            target.write(payload)
    else:
        path.write_bytes(payload)
    print(f'SAVED {path} count={len(standard)} parses={dict(parses)} bytes={path.stat().st_size}', flush=True)


if __name__ == '__main__':
    main()
