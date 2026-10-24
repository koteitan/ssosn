"""Exact standardness table, including negatives, in a packed JSON format.

Run: timeout 1500 python3 work/stdtok_data.py --N 9
Index at length k is the base-6 numeral of a word in ALPHABET order.
Each bit (least significant first) records standardness; zero includes every
non-standard word, not just words visited by the oracle. All words lie below P.

Pruning uses prefix closure (§24): fs(S,1) decrements the final positive entry;
decrementing and deleting terminal zeros reaches every prefix. Thus a standard
extension cannot have a non-standard prefix. No candidate grammar is used.
"""
import argparse
import base64
import gzip
from functools import lru_cache
import json
from pathlib import Path
import time

ALPHABET = ('A0', 'A1', 'A2', 'A3', 'E1', 'W')
HERE = Path(__file__).resolve().parent


def read_data(path):
    opener = gzip.open if str(path).endswith('.gz') else open
    with opener(path, 'rt', encoding='utf-8') as source:
        data = json.load(source)
    if data['format'] != 'stdtok-bits-v1':
        raise ValueError('unsupported table format')
    return data


def bit_rows(data):
    return [(row['length'], base64.b64decode(row['bits_base64']))
            for row in data['levels']]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--N', '-N', type=int, default=9)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--no-reuse', action='store_true')
    parser.add_argument('--no-cut-cache', action='store_true',
                        help='disable memoization of exact Seq.cut results')
    args = parser.parse_args()
    if not 0 <= args.N <= 10:
        parser.error('N must be between 0 and 10')
    import std
    import token_laws as laws

    # The greedy descents revisit the same sequences. Cache the original cut,
    # not an alternative cut rule. This patch is confined to this CLI process.
    if not args.no_cut_cache:
        sequence_class = std.harness.Seq
        original_cut = sequence_class.cut

        @lru_cache(maxsize=32768)
        def cached_cut(sequence, mode):
            return original_cut(sequence_class(sequence, mode))

        sequence_class.cut = lambda self: cached_cut(self.S, self.mode)

    if not std.is_standard(laws.BASE):
        raise RuntimeError('the empty-word base is not standard')

    known = set()
    reference = HERE / 'token-laws-check.json'
    if not args.no_reuse and reference.exists():
        known = {tuple(row['tokens']) for row in
                 json.loads(reference.read_text())['rows']}
    start = time.monotonic()
    frontier = [((), 0)]
    levels = []
    calls = reused = 0
    for length in range(args.N + 1):
        bits = bytearray((6 ** length + 7) // 8)
        for word, code in frontier:
            bits[code >> 3] |= 1 << (code & 7)
        count = len(frontier)
        levels.append(dict(length=length, total=6 ** length,
                           standard=count, nonstandard=6 ** length-count,
                           bits_base64=base64.b64encode(bits).decode('ascii')))
        print(f'length={length} standard={count} nonstandard={6**length-count}'
              f' oracle_calls={calls} reused={reused}'
              f' elapsed={time.monotonic()-start:.1f}s', flush=True)
        if length == args.N:
            break
        following = []
        for prefix, code in frontier:
            for digit, token in enumerate(ALPHABET):
                word = prefix + (token,)
                if word in known:
                    okay = True
                    reused += 1
                else:
                    calls += 1
                    okay = std.is_standard(laws.seq(word))
                if okay:
                    following.append((word, code*6+digit))
        frontier = following
    data = dict(format='stdtok-bits-v1', alphabet=ALPHABET, max_tokens=args.N,
                includes_empty=True, upper_bound=list(laws.HI),
                domain='all Cartesian words; every raw word is below upper_bound',
                method='std.is_standard + standard-prefix closure (§24)',
                cut_cache=not args.no_cut_cache,
                reused_source='token-laws-check.json' if known else None,
                oracle_calls=calls, reused_positive_rows=reused,
                elapsed_seconds=time.monotonic()-start, levels=levels,
                total=sum(row['total'] for row in levels),
                standard=sum(row['standard'] for row in levels),
                nonstandard=sum(row['nonstandard'] for row in levels))
    payload = (json.dumps(data, ensure_ascii=False, separators=(',', ':'))+'\n').encode()
    path = args.out or HERE / f'stdtok-{args.N}.json'
    if len(payload) > 1_000_000 and not str(path).endswith('.gz'):
        path = Path(str(path)+'.gz')
    if str(path).endswith('.gz'):
        with gzip.open(path, 'wb') as target:
            target.write(payload)
    else:
        path.write_bytes(payload)
    print(f'saved {path.name}: total={data["total"]} standard={data["standard"]}'
          f' nonstandard={data["nonstandard"]} bytes={path.stat().st_size}', flush=True)


if __name__ == '__main__':
    main()
