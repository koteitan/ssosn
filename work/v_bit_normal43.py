"""Candidate recursive grammar for canonical W/D/V bit words.

This is an experiment: a positive block is reduced by T or T2; double-zero
separators join non-increasing principal blocks, and terminal zeros are
successors.  Run: timeout 60 python3 work/v_bit_normal43.py --tokens 10
"""
import argparse
from functools import lru_cache
from itertools import product
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import conj2
import std
import v_bits43
from v_constraints_real43 import RAW


def split_blocks(bits):
    blocks = []
    start = 0
    i = 0
    while i+1 < len(bits):
        if bits[i:i+2] == (0, 0):
            blocks.append(bits[start:i])
            i += 2
            start = i
        else:
            i += 1
    blocks.append(bits[start:])
    return blocks


@lru_cache(maxsize=None)
def canon(bits):
    bits = tuple(bits)
    if not bits or all(x == 0 for x in bits):
        return True
    while bits and bits[-1] == 0:
        bits = bits[:-1]
    if bits[0] == 0:
        return False
    blocks = split_blocks(bits)
    if any(not block or block[0] == 0 or not canon_block(block)
           for block in blocks):
        return False
    # Canonical principal blocks have the same lexicographic and ordinal
    # order in the bounded audit.  Using lex order keeps this a syntactic
    # candidate grammar; the general order theorem is still unproved.
    return all(a >= b for a, b in zip(blocks, blocks[1:]))


@lru_cache(maxsize=None)
def canon_block(block):
    lowered = conj2.T(block)
    if lowered != block:
        return canon(lowered)
    try:
        return canon(v_bits43.T2(block))
    except ValueError:
        return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tokens', type=int, default=10)
    args = ap.parse_args()
    counts = {'agree_standard': 0, 'agree_nonstandard': 0,
              'false_accept': 0, 'false_reject': 0}
    examples = {k: [] for k in counts}
    for length in range(2, args.tokens+1):
        for tail in product('WDV', repeat=length-2):
            word = ('D', 'V') + tail
            if any(word[i] == 'V' and word[i-1] != 'D'
                   for i in range(2, len(word))):
                continue
            raw = (0, 0, 2, 1) + tuple(x for t in word for x in RAW[t])
            actual = std.is_standard(raw)
            predicted = canon(v_bits43.bits(word))
            key = ('agree_standard' if actual else 'agree_nonstandard') if actual == predicted else ('false_accept' if predicted else 'false_reject')
            counts[key] += 1
            if len(examples[key]) < 15:
                examples[key].append(''.join(word))
    print(counts)
    for key in ('false_accept', 'false_reject'):
        print(key, examples[key])
    # A grammar-level closure check for the final V / bit 2 law.
    v_checked = v_bad = 0
    for length in range(1, 9):
        for bits in product((0, 1, 2), repeat=length):
            if bits[-1] != 2 or not canon(bits):
                continue
            for n in range(1, 11):
                v_checked += 1
                if not canon(bits[:-1] + (1,) * n):
                    v_bad += 1
    print('V replacement closure', v_checked, 'checked', v_bad, 'bad')


if __name__ == '__main__':
    main()
