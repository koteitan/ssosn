"""Test the root shift P -> P1 on standard words through raw length 18.

Run after p1_tokens43.py and p2_tokens44.py:
  timeout 600 python3 work/p2_shift44.py
"""
from collections import Counter, defaultdict
from functools import lru_cache
import gzip
import json
from pathlib import Path
import time

import harness
import std
import p1_tokens43 as old
import p2_tokens44 as new

HERE = Path(__file__).resolve().parent
OLD_P, OLD_P1 = old.P, old.P1
NEW_P, NEW_P1 = new.P, new.P1
assert OLD_P1 == NEW_P


def read_json(path):
    if path.suffix == '.gz':
        with gzip.open(path, 'rt') as f:
            return json.load(f)
    return json.loads(path.read_text())


def read_table(stem):
    for suffix in ('.json', '.json.gz', '.gz'):
        path = HERE / (stem + suffix)
        if path.exists():
            return read_json(path)
    raise FileNotFoundError(stem)


def text(raw):
    return ''.join(map(str, raw))


def x_from(raw, root):
    assert tuple(raw[:len(root)]) == tuple(root)
    return tuple(raw[len(root):])


def show_pair(x, source, shifted, status_source, status_shifted):
    try:
        cut_source = harness.Seq(source, 'new').cut()
        terms_source = [harness.fs(source, n) for n in (1, 2)]
    except Exception as exc:
        cut_source = f'ERROR:{type(exc).__name__}'
        terms_source = []
    try:
        cut_shifted = harness.Seq(shifted, 'new').cut()
        terms_shifted = [harness.fs(shifted, n) for n in (1, 2)]
    except Exception as exc:
        cut_shifted = f'ERROR:{type(exc).__name__}'
        terms_shifted = []
    return {
        'X': text(x),
        'source': text(source), 'shifted': text(shifted),
        'source_standard': status_source, 'shifted_standard': status_shifted,
        'cut_source': cut_source, 'cut_shifted': cut_shifted,
        'source_terms_1_2': [text(t) for t in terms_source],
        'shifted_terms_1_2': [text(t) for t in terms_shifted],
    }


def main():
    started = time.monotonic()
    p1_data = read_table('p1-tokens43-18')
    p2_data = read_table('p2-tokens44-18')
    source_words = sorted((tuple(map(int, s)) for s in p1_data['standard_raw']),
                          key=lambda s: (len(s), s))
    target_words = sorted((tuple(map(int, s)) for s in p2_data['standard_raw']),
                          key=lambda s: (len(s), s))

    # Cache cuts shared by std.is_standard, fs, and the diagnostic samples.
    original_cut = harness.Seq.cut
    @lru_cache(maxsize=250000)
    def cached_cut(raw, mode):
        return original_cut(harness.Seq(raw, mode))
    harness.Seq.cut = lambda self: cached_cut(self.S, self.mode)

    forward = Counter()
    reverse = Counter()
    forward_bad = []
    reverse_bad = []
    pairs = []
    target_status = {}

    # (a) Every P+X standard word maps to P1+X?
    for source in source_words:
        x = x_from(source, OLD_P)
        shifted = NEW_P + x
        shifted_std = std.is_standard(shifted)
        target_status[x] = shifted_std
        forward['shifted_standard' if shifted_std else 'shifted_nonstandard'] += 1
        forward[f'source_length_{len(source)}'] += 1
        if shifted_std:
            pairs.append((x, source, shifted))
        else:
            forward_bad.append((x, source, shifted, True, False))

    # (b) Conversely, every P1+X standard word has P+X standard?
    for shifted in target_words:
        x = x_from(shifted, NEW_P)
        source = OLD_P + x
        source_std = std.is_standard(source)
        reverse['source_standard' if source_std else 'source_nonstandard'] += 1
        reverse[f'target_length_{len(shifted)}'] += 1
        if not source_std:
            reverse_bad.append((x, source, shifted, False, True))

    # (c) On standard pairs, compare the actual tails of terms n=1..5.
    expansion = Counter()
    cuts = Counter()
    own_root_cuts = Counter()
    expansion_bad = []
    pair_depths = Counter()
    for x, source, shifted in pairs:
        cut_source = harness.Seq(source, 'new').cut()
        cut_shifted = harness.Seq(shifted, 'new').cut()
        root_source = cut_source <= len(NEW_P)
        root_shifted = cut_shifted <= len(NEW_P)
        source_inside_own_root = cut_source <= len(OLD_P)
        shifted_inside_own_root = cut_shifted <= len(NEW_P)
        cut_kind = ('both_root' if root_source and root_shifted else
                    'source_root' if root_source else
                    'shift_root' if root_shifted else 'both_after_root')
        cuts[cut_kind] += 1
        own_root_cuts[
            ('source_in_own_root' if cut_source <= len(OLD_P) else 'source_after_own_root')
            + '__' +
            ('shifted_in_own_root' if cut_shifted <= len(NEW_P) else 'shifted_after_own_root')
        ] += 1
        source_rooted_all = True
        pair_mismatches = []
        for n in range(1, 6):
            term_source = harness.fs(source, n)
            term_shifted = harness.fs(shifted, n)
            if term_source[:len(OLD_P)] != OLD_P:
                expansion['source_term_not_P_prefixed'] += 1
                source_rooted_all = False
                continue
            expansion['source_term_P_prefixed'] += 1
            x_n = term_source[len(OLD_P):]
            expected = NEW_P + x_n
            if term_shifted == expected:
                expansion['tail_agree'] += 1
                expansion[f'tail_agree_n{n}'] += 1
            else:
                expansion['tail_differ'] += 1
                expansion[f'tail_differ_n{n}'] += 1
                pair_mismatches.append((n, term_source, term_shifted, expected))
        if source_rooted_all:
            pair_depths['source_rooted_all_n1_n5'] += 1
        else:
            pair_depths['some_source_term_leaves_P'] += 1
        if pair_mismatches:
            expansion['pairs_with_difference'] += 1
            expansion[f'pairs_with_difference__{cut_kind}'] += 1
            expansion[
                'pairs_with_difference__' +
                ('source_own_root' if source_inside_own_root else 'source_after_own_root') + '__' +
                ('shifted_own_root' if shifted_inside_own_root else 'shifted_after_own_root')
            ] += 1
            expansion_bad.append((x, source, shifted, pair_mismatches))
        else:
            expansion['pairs_all_checked_terms_agree'] += 1

    def detail_rows(rows, kind):
        rows = sorted(rows, key=lambda row: (len(row[0]), row[0]))[:5]
        out = []
        for x, source, shifted, source_std, shifted_std, *rest in rows:
            row = show_pair(x, source, shifted, source_std, shifted_std)
            if kind == 'expansion':
                row['mismatch_terms'] = [
                    {'n': n, 'source_term': text(src_term),
                     'shifted_term': text(dst_term), 'expected_shifted': text(expect)}
                    for n, src_term, dst_term, expect in rest[0]
                ]
            out.append(row)
        return out

    a_examples = detail_rows(forward_bad, 'standardness')
    b_examples = detail_rows(reverse_bad, 'standardness')
    c_examples = detail_rows([
        (x, source, shifted, True, True, mismatches)
        for x, source, shifted, mismatches in expansion_bad
    ], 'expansion')

    print('source [P,P1) words', len(source_words))
    print('(a) shifted standardness', dict(forward), 'mismatches', len(forward_bad))
    print(' (a) shortest mismatches', a_examples)
    print('target [P1,P2) words', len(target_words))
    print('(b) reverse standardness', dict(reverse), 'mismatches', len(reverse_bad))
    print(' (b) shortest mismatches', b_examples)
    print('both-standard pairs', len(pairs))
    print('(c) expansion counts', dict(expansion), 'cuts', dict(cuts),
          'own-root cuts', dict(own_root_cuts), 'pair flags', dict(pair_depths))
    print(' (c) shortest mismatches', c_examples)
    print('elapsed', round(time.monotonic() - started, 2), 'seconds')


if __name__ == '__main__':
    main()
