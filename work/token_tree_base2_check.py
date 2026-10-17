"""Recheck the 13056 base-(2) parent/term values with CNF-tree state."""
import csv
import gzip
import json
from pathlib import Path
import token_tree as T
from token_targets import pretty
from ordinal import cmp

HERE=Path(__file__).resolve().parent


def main():
    counts=dict(agree=0,differ=0,adjacent_violations=0)
    changed=[]
    previous=None
    with gzip.open(HERE/'token-base2-values.tsv.gz','rt') as stream:
        for row in csv.DictReader(stream,delimiter='\t'):
            s=tuple(map(int,row['sequence']))
            x=T.value(s)
            tag='agree' if pretty(x)==row['value'] else 'differ'
            counts[tag]+=1
            if tag!='agree':changed.append(row['sequence'])
            if previous is not None and cmp(previous,x)>=0:counts['adjacent_violations']+=1
            previous=x
    (HERE/'token-tree-base2-check.json').write_text(json.dumps(dict(counts=counts,changed=changed),ensure_ascii=False,indent=2)+'\n')
    print(counts)


if __name__=='__main__':main()
