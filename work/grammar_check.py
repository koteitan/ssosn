"""Compare MODULE.accept(tokens) against all words in a stdtok table.

timeout 60 python3 work/grammar_check.py grammar_example [--N 9] [--raw]
--raw calls accept(tokens, raw_sequence), where raw_sequence includes (0,0,2,1).
MODULE may be an import name or a Python file. No pruning by the candidate.
Mismatch order: token count, then lexicographic token-tuple order (alphabet order).
"""
import argparse
import importlib
import importlib.util
import itertools
from pathlib import Path
import time

from stdtok_data import HERE, bit_rows, read_data


def load_module(name):
    if name.endswith('.py') or '/' in name:
        path = Path(name).resolve()
        spec = importlib.util.spec_from_file_location('candidate_grammar', path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module
    return importlib.import_module(name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('module')
    parser.add_argument('--N', '-N', type=int, default=9)
    parser.add_argument('--data', type=Path)
    parser.add_argument('--raw', action='store_true')
    args = parser.parse_args()
    path = args.data or HERE / f'stdtok-{args.N}.json'
    if not path.exists() and Path(str(path)+'.gz').exists():
        path = Path(str(path)+'.gz')
    if not path.exists():
        parser.error(f'missing {path.name}; run stdtok_data.py --N {args.N} first')
    data = read_data(path)
    if data['max_tokens'] < args.N:
        parser.error('table does not cover requested N')
    accept = load_module(args.module).accept
    if args.raw:
        from token_laws import seq
    counts = [[0, 0], [0, 0]]  # actual standardness, predicted acceptance
    fn, fp = [], []
    alphabet = tuple(data['alphabet'])
    start = time.monotonic()
    for length, bits in bit_rows(data):
        if length > args.N:
            break
        for code, tokens in enumerate(itertools.product(alphabet, repeat=length)):
            actual = (bits[code >> 3] >> (code & 7)) & 1
            try:
                predicted = accept(tokens, seq(tokens)) if args.raw else accept(tokens)
            except Exception as error:
                raise RuntimeError(f'accept failed for {tokens!r}') from error
            if not isinstance(predicted, bool):
                raise TypeError(f'accept{tokens!r} returned {predicted!r}, expected bool')
            counts[actual][predicted] += 1
            if actual and not predicted and len(fn) < 20:
                fn.append(tokens)
            elif predicted and not actual and len(fp) < 20:
                fp.append(tokens)
    print('actual / predicted       rejected    accepted')
    print(f'non-standard          {counts[0][0]:11d} {counts[0][1]:11d}')
    print(f'standard              {counts[1][0]:11d} {counts[1][1]:11d}')
    for title, examples in [('standard but rejected', fn), ('accepted but non-standard', fp)]:
        print(f'{title}: first {len(examples)}')
        for word in examples:
            print(f'  {len(word)}: {word!r}')
    print(f'total={sum(map(sum, counts))} elapsed={time.monotonic()-start:.3f}s')


if __name__ == '__main__':
    main()
