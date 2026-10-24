"""Record all standard-prefix extensions in P <= raw < 0021021.

timeout 600 python3 work/above_p_data26.py --N 7
The first D counts as one token. Distinct spellings are retained; standardness
and subsequent value references refer to the raw sequence. No grammar prunes.
"""
import argparse
from functools import lru_cache
import gzip
import json
from pathlib import Path
import time

import std
import token_tree as T

HERE = Path(__file__).resolve().parent
ALPHABET = ('A0','A1','A2','A3','E1','W','D')
BASE = (0,0,2,1)
P = BASE+(0,2)
UPPER = P+(1,)


def raw(tokens):
    return BASE+T.raw_tokens(tuple(tokens))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--N',type=int,default=7)
    parser.add_argument('--out',type=Path,default=HERE/'above-p26-data.json.gz')
    args=parser.parse_args()
    if not 2<=args.N<=10:
        parser.error('N must be 2..10')
    seq_class=std.harness.Seq
    original_cut=seq_class.cut
    @lru_cache(maxsize=32768)
    def cut(s,mode):return original_cut(seq_class(s,mode))
    seq_class.cut=lambda self:cut(self.S,self.mode)
    @lru_cache(maxsize=100000)
    def oracle(s):return std.is_standard(s)
    start=time.monotonic()
    assert oracle(BASE) and oracle(P)
    frontier=[('D',)]
    rows=[dict(tokens=('D',),standard=True)]
    levels=[dict(length=1,candidates=1,standard=1,nonstandard=0)]
    for size in range(2,args.N+1):
        following=[];accepted=0;tested=0
        for prefix in frontier:
            for token in ALPHABET:
                word=prefix+(token,)
                sequence=raw(word)
                assert P<=sequence<UPPER
                standard=oracle(sequence)
                rows.append(dict(tokens=word,standard=standard))
                tested+=1
                if standard:
                    accepted+=1
                    following.append(word)
        frontier=following
        levels.append(dict(length=size,candidates=tested,standard=accepted,nonstandard=tested-accepted))
        report=dict(alphabet=ALPHABET,max_tokens=size,requested_max_tokens=args.N,
            lower_bound=P,lower_inclusive=True,upper_bound=UPPER,upper_inclusive=False,
            scope='all word spellings starting D with standard immediate prefix; first D counts',
            standardness='std.is_standard, exact cut memoization; no valuation used',
            levels=levels,rows=rows,elapsed_seconds=time.monotonic()-start,
            standard=sum(r['standard'] for r in rows),nonstandard=sum(not r['standard'] for r in rows),
            unique_raw_sequences=len({raw(r['tokens']) for r in rows}),
            unique_standard_sequences=len({raw(r['tokens']) for r in rows if r['standard']}))
        pending=args.out.with_name(args.out.name+'.pending')
        with gzip.open(pending,'wt',encoding='utf-8') as target:
            json.dump(report,target,ensure_ascii=False,separators=(',',':'))
        pending.replace(args.out)
        print(levels[-1],f'elapsed={time.monotonic()-start:.1f}s',flush=True)
    print('saved',args.out.name,'standard',report['standard'],'nonstandard',report['nonstandard'],
          'unique_standard',report['unique_standard_sequences'],flush=True)


if __name__=='__main__':main()
