"""Cross-check stable F values on D^10 A0 and D^11 A0 references.

timeout 180 python3 work/reltail31_d11_check.py
Only already stable tails of length <= 6 are retried; unresolved tails remain so.
"""
import collections
import gzip
import json
import time
from pathlib import Path

import token_tree as T
from above_p_data26 import HERE, raw
from reltail31_reference import Reference, Undecided, memoize_cut
from token_targets import pretty


def freeze(x):
    return tuple(freeze(y) for y in x) if isinstance(x, list) else x


def main():
    memoize_cut()
    data=json.load(gzip.open(HERE/'reltail31-common.json.gz','rt'))
    rows=[r for r in data['rows'] if r['status']=='stable3_5_7'
          and 'common-reference-language' in r['source'] and len(r['tail'])<=6]
    result=[];base=raw(('D',)*11+('A0',));start=time.monotonic()
    for row in rows:
        tail=T.raw_tokens(row['tail'])
        try:
            v5=Reference(base,samples=5,seconds=1.5,max_nodes=50000,
                         max_memo=100000).evaluate(tail)
            v7=Reference(base,samples=7,seconds=1.5,max_nodes=50000,
                         max_memo=100000).evaluate(tail)
            v10=freeze(row['value'])
            status='agree' if v5==v10==v7 else 'differ'
            result.append(dict(tail=row['tail'],status=status,
                value10=row['pretty'],value11=pretty(v5),value117=pretty(v7)))
        except Undecided as e:
            result.append(dict(tail=row['tail'],status='unresolved',reason=str(e)))
    report=dict(total=len(rows),counts=dict(collections.Counter(r['status'] for r in result)),
                rows=result,seconds=time.monotonic()-start)
    (HERE/'reltail31-d11-check.json').write_text(
        json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(report['counts'],'seconds',round(report['seconds'],2),flush=True)


if __name__=='__main__':main()
