"""Bounded structural exchange of periodic copy words with T and T2.

Run: timeout 60 python3 work/v_exchange43.py --tokens 13 --terms 6
T2 is tested only on one principal block, with every run starting in 2.
"""
import argparse
from collections import Counter
from pathlib import Path
import sys
HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]
import conj2
import v_bits43
from v_inequality43 import words_u
from v_symbolic_cut43 import classify, symbolic_term
from v_bit_normal43 import canon


def bit(word):
    return v_bits43.bits(word)


def principal_t2(b):
    if len(conj2.units(b)) != 1 or conj2.T(b) != b:
        return None
    try:
        return v_bits43.T2(b)
    except ValueError:
        return None


def test(word, terms, counts, failures):
    kind, pos = classify(word)
    if kind not in ('D_ROOT', 'D_W_HEAD'):
        return
    if kind == 'D_ROOT':
        a = bit(word[:-1]); h = None
        q = a
        parent = a+(1,)
        ends_positive = bool(a) and a[-1] != 0
        def expected(f, n):
            fa = f(a)
            return fa+((0,)+fa)*(n-1)
        def expected_parent(f):
            return f(a)+(1,)
    else:
        h = bit(word[:pos]); q = bit(word[pos+1:-1])
        parent = h+(0,)+q+(1,)
        ends_positive = bool(q) and q[-1] != 0
        def expected(f, n):
            return f(h)+((0,)+f(q))*n
        def expected_parent(f):
            return f(h)+(0,)+f(q)+(1,)
    counts[kind+'_words'] += 1
    counts[kind+'_positive_ending' if ends_positive else kind+'_zero_or_empty_ending'] += 1
    if conj2.T(parent) == expected_parent(conj2.T):
        counts[kind+'_T_parent_exchange'] += 1
    elif ends_positive:
        failures.append(('T_parent', ''.join(word)))
    for n in range(1, terms+1):
        child = bit(symbolic_term(word,n,kind,pos))
        if conj2.T(child) != expected(conj2.T,n):
            failures.append(('T_term',''.join(word),n))
        counts[kind+'_T_term'] += 1
    if ends_positive:
        lowered = conj2.T(parent)
        core = lowered[1:] if lowered and lowered[0] == 0 else lowered
        if not canon(core):
            counts[kind+'_T_parent_outside_L'] += 1
        for n in range(1, terms+1):
            lowered_term = conj2.T(bit(symbolic_term(word,n,kind,pos)))
            core = lowered_term[1:] if lowered_term and lowered_term[0] == 0 else lowered_term
            if not canon(core):
                counts[kind+'_T_terms_outside_L'] += 1
    t2p = principal_t2(parent)
    if t2p is not None:
        counts[kind+'_T2_parent_defined'] += 1
        if t2p != expected_parent(v_bits43.T2):
            failures.append(('T2_parent',''.join(word)))
        for n in range(1, terms+1):
            child = bit(symbolic_term(word,n,kind,pos))
            t2c = principal_t2(child)
            if t2c != expected(v_bits43.T2,n):
                failures.append(('T2_term',''.join(word),n))
            counts[kind+'_T2_term'] += 1


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--tokens',type=int,default=13)
    p.add_argument('--terms',type=int,default=6)
    args=p.parse_args()
    counts=Counter(); failures=[]
    for core in words_u(args.tokens):
        if core[-1] != 'D': continue
        for prefix in ((),('W',)):
            test(prefix+core,args.terms,counts,failures)
    print(dict(counts))
    print('failures',len(failures),failures[:20])

if __name__=='__main__': main()
