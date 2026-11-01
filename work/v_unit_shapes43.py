"""Classify N<=13 L union W L limits by their actual first three terms.

Run: timeout 600 python3 work/v_unit_shapes43.py
Class formulas are accepted only if real_copy_word agrees at n=1,2,3.
The JSON stores exact-signature counts and one shortest witness each.
"""
import json
from collections import Counter, defaultdict
from functools import lru_cache
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import conj2
import harness
import ordinal
import p1_token_cut43 as token_cut
import v_bits43
from p1_tokens43 import BASE as RAW_BASE
from v_inequality43 import words_u
from v_constraints_real43 import RAW, real_copy_word
from v_symbolic_cut43 import grammar_class

MAX_TOKENS = 13
PREFIXES = ((), ('W',))
LIMITS = frozenset(('V', 'D'))


def unit_spans(y):
    us = conj2.units(y)
    spans = []
    pos = 0
    for unit in us:
        spans.append((pos, pos + len(unit)))
        pos += len(unit)
    if pos != len(y):
        raise AssertionError(('units do not cover bits', y, us, pos))
    return us, spans


@lru_cache(maxsize=None)
def bits(word):
    return v_bits43.bits(word)


@lru_cache(maxsize=None)
def rank(word):
    return v_bits43.v2(bits(word))


def unit_reduction(unit):
    lowered = conj2.T(unit)
    t2 = None
    if lowered == tuple(unit) and unit != (0,):
        try:
            t2 = v_bits43.T2(unit)
        except ValueError:
            pass
    return {'unit': list(unit), 'T': list(lowered),
            'T2_if_T_fixed': None if t2 is None else list(t2)}


def candidate_term(word, cls, pos, n):
    if cls == 'R1':
        return word[:-1] + ('D',) * n
    if cls == 'R2':
        u = word[:-1]
        return u + (('W',) + u) * (n - 1)
    if cls == 'R3':
        h = word[:pos]
        q = word[pos + 1:-1]
        return h + (('W',) + q) * n
    raise ValueError(cls)


def match_classes(word, real_terms):
    matches = []
    if word[-1] == 'V':
        if all(candidate_term(word, 'R1', None, n) == real_terms[n-1]
               for n in (1, 2, 3)):
            matches.append(('R1', None))
    elif word[-1] == 'D':
        if all(candidate_term(word, 'R2', None, n) == real_terms[n-1]
               for n in (1, 2, 3)):
            matches.append(('R2', None))
        for pos, token in enumerate(word[:-1]):
            if token != 'W':
                continue
            if all(candidate_term(word, 'R3', pos, n) == real_terms[n-1]
                   for n in (1, 2, 3)):
                matches.append(('R3', pos))
    return matches


def token_predict_cut(word, raw):
    # Start the local token parser after the initial W or D root token.
    # p1_token_cut43 normally fixes P=(0,0,2,1,D), while W L words have
    # prefix (0,0,2,1,W) before their remaining D V ... token suffix.
    tokens = word[1:]
    token_cut.P = RAW_BASE + RAW[word[0]]
    if word[-1] == 'V':
        return token_cut.heads(tokens, RAW)[-1][1]
    if token_cut.br3_from_tokens(tokens):
        return token_cut.third_parent_cut(raw, tokens, RAW)[2]
    return token_cut.d_cut(tokens, RAW)[1]


def describe(word):
    real_terms = tuple(real_copy_word(word, n) for n in (1, 2, 3))
    matches = match_classes(word, real_terms)
    if not matches:
        return {'word': ''.join(word), 'class': 'OTHER',
                'y': list(bits(word)),
                'units': [list(u) for u in unit_spans(bits(word))[0]],
                'rank': ordinal.show(rank(word)),
                'terms': [{'n': n, 'c': ''.join(t), 'y': list(bits(t)),
                           'units': [list(u) for u in unit_spans(bits(t))[0]],
                           'rank': ordinal.show(rank(t))}
                          for n, t in enumerate(real_terms, 1)],
                '_sort': (len(word), word)}

    r3_positions = [pos for cls, pos in matches if cls == 'R3']
    # For multiple R3 matches retain all, and use the rightmost for the row.
    chosen = (('R3', max(r3_positions)) if r3_positions else matches[0])
    cls, pos = chosen
    y = bits(word)
    if cls == 'R1':
        s = max(i for i, b in enumerate(y) if b == 2)
        trailing_zero = None
    elif cls == 'R2':
        a = bits(word[:-1])
        s = 0
        trailing_zero = bool(a) and a[-1] == 0
    else:
        h = bits(word[:pos])
        q = bits(word[pos + 1:-1])
        s = len(h)
        trailing_zero = (not q) or q[-1] == 0

    units, spans = unit_spans(y)
    reductions = [unit_reduction(unit) for unit in units]
    hit = next((j for j, (lo, hi) in enumerate(spans, 1) if lo <= s < hi), None)
    if hit is None:
        raise AssertionError(('copy position outside units', word, cls, pos,
                              s, units, spans))
    at_start = spans[hit - 1][0] == s

    terms = []
    preserved = []
    for n, actual_tokens in enumerate(real_terms, 1):
        yn = bits(actual_tokens)
        un, _ = unit_spans(yn)
        kept = len(un) >= hit - 1 and tuple(un[:hit - 1]) == tuple(units[:hit - 1])
        preserved.append(kept)
        terms.append({'n': n, 'c': ''.join(actual_tokens), 'y': list(yn),
                      'units': [list(u) for u in un],
                      'rank': ordinal.show(rank(actual_tokens))})

    sig = (cls, len(units), hit, at_start, trailing_zero,
           *(len(x['units']) for x in terms))
    return {
        'word': ''.join(word), 'class': cls,
        'all_matching_classes': [[c, p] for c, p in matches],
        'chosen_r3_positions': r3_positions,
        'y': list(y), 'units': [list(u) for u in units],
        'unit_reductions': reductions, 's0': s, 'unit_index': hit,
        's_is_unit_start': at_start, 'prefix_units_unchanged': preserved,
        'trailing_zero': trailing_zero, 'signature': list(sig),
        'rank': ordinal.show(rank(word)), 'terms': terms,
        '_sort': (len(word), word),
    }


def main():
    words = set()
    for core in words_u(MAX_TOKENS):
        if core[-1] not in LIMITS:
            continue
        for prefix in PREFIXES:
            words.add(prefix + core)

    all_rows = [describe(w) for w in sorted(words, key=lambda w: (len(w), w))]
    other = [r for r in all_rows if r['class'] == 'OTHER']
    groups_by_sig = defaultdict(list)
    class_counts = Counter()
    r3_multi = 0
    r2_r3_overlap = 0
    grammar_matches = Counter()
    token_cut_counts = Counter()
    token_cut_by_prefix = Counter()
    token_cut_examples = []

    for row in all_rows:
        class_counts[row['class']] += 1
        if row['class'] == 'OTHER':
            continue
        if len(row['chosen_r3_positions']) > 1:
            r3_multi += 1
        if any(x[0] == 'R2' for x in row['all_matching_classes']) and row['chosen_r3_positions']:
            r2_r3_overlap += 1

        gclass, gpos = grammar_class(tuple(row['word']))
        gmap = {'V_HEAD': 'R1', 'D_ROOT': 'R2', 'D_W_HEAD': 'R3'}
        chosen_pos = (max(row['chosen_r3_positions'])
                      if row['class'] == 'R3' else None)
        agrees = gmap.get(gclass) == row['class'] and gpos == chosen_pos
        grammar_matches['agree' if agrees else 'differ'] += 1

        raw = RAW_BASE + tuple(x for t in row['word'] for x in RAW[t])
        predicted = token_predict_cut(tuple(row['word']), raw)
        actual = harness.Seq(raw, 'new').cut()
        verdict = 'agree' if predicted == actual else 'differ'
        token_cut_counts[verdict] += 1
        token_cut_by_prefix[(row['word'][0], verdict)] += 1
        if predicted != actual and len(token_cut_examples) < 20:
            token_cut_examples.append({'c': row['word'], 'predicted': predicted,
                                       'actual': actual})
        groups_by_sig[tuple(row['signature'])].append(row)

    coarse = len(groups_by_sig) > 50
    groups = defaultdict(list)
    if coarse:
        for sig, rows in groups_by_sig.items():
            cls, k, j, starts, trailing, *counts = sig
            key = (cls, 'j=k' if j == k else 'j<k', starts, trailing, *counts)
            groups[key].extend(rows)
    else:
        groups.update(groups_by_sig)

    summary = []
    for sig, rows in sorted(groups.items(), key=lambda item: repr(item[0])):
        sample = min(rows, key=lambda r: r['_sort'])
        unchanged = Counter(''.join('1' if x else '0'
                                    for x in r['prefix_units_unchanged'])
                            for r in rows)
        reductions = Counter(
            ('T2' if x['T2_if_T_fixed'] is not None else
             'T-fixed' if x['T'] == x['unit'] else 'T-lowered')
            for r in rows for x in r['unit_reductions'])
        summary.append({
            'signature': list(sig), 'count': len(rows),
            'prefix_units_unchanged_n1_n3': dict(sorted(unchanged.items())),
            'unit_reduction_counts': dict(sorted(reductions.items())),
            'shortest_example': {
                'c': sample['word'], 'y': sample['y'], 'units_y': sample['units'],
                'matching_classes': sample['all_matching_classes'],
                'R3_positions': sample['chosen_r3_positions'],
                'unit_reductions': sample['unit_reductions'], 's0': sample['s0'],
                'unit_index': sample['unit_index'],
                's_is_unit_start': sample['s_is_unit_start'],
                'prefix_units_unchanged_n1_n3': sample['prefix_units_unchanged'],
                'trailing_zero': sample['trailing_zero'],
                'v2_c': sample['rank'], 'terms': sample['terms'],
            },
        })

    other_examples = [{k: r[k] for k in ('word', 'y', 'units', 'rank', 'terms')}
                      for r in other[:5]]
    report = {
        'max_tokens': MAX_TOKENS, 'input_words': len(words),
        'class_counts': dict(class_counts), 'OTHER_count': len(other),
        'OTHER_shortest_examples': other_examples,
        'multiple_R3_match_words': r3_multi,
        'overlap_R2_R3_words': r2_r3_overlap,
        'grammar_class_agreement': dict(grammar_matches),
        'token_only_cut_agreement': dict(token_cut_counts),
        'token_only_cut_agreement_by_initial_token': {
            f'{token}_{verdict}': count
            for (token, verdict), count in sorted(token_cut_by_prefix.items())},
        'token_only_cut_first_differences': token_cut_examples,
        'exact_signature_count': len(groups_by_sig),
        'used_coarse_signatures': coarse, 'group_count': len(groups),
        'groups': summary,
    }
    out = HERE / 'v-unit-shapes43.json'
    out.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print('input words', len(words), 'classes', dict(class_counts),
          'R3 multiple', r3_multi, 'R2/R3 overlap', r2_r3_overlap)
    print('grammar_class agreement', dict(grammar_matches))
    print('token-only cut agreement', dict(token_cut_counts),
          'by initial token', {f'{a}_{b}': n for (a,b),n in token_cut_by_prefix.items()},
          'differences', token_cut_examples[:5])
    print('signatures', len(groups_by_sig), 'coarse', coarse,
          'groups', len(groups), 'bytes', out.stat().st_size)
    print('OTHER examples', [r['word'] for r in other[:5]])
    for row in summary:
        print(row['signature'], row['count'], row['shortest_example']['c'])


if __name__ == '__main__':
    main()
