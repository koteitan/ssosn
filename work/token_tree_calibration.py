"""Repeat finite cofinal calibration on all 17828 original token inputs."""
import collections
import json
from pathlib import Path
import harness
import evalord as E
import token_tree as T

HERE=Path(__file__).resolve().parent


def main():
    source=json.loads((HERE/'token-laws-check.json').read_text())
    counts=collections.Counter()
    failed=[]
    for i,row in enumerate(source['rows'],1):
        s=tuple(map(int,row['sequence']))
        parent=T.value(s)
        cut=harness.Seq(s,'new').cut()
        g,b=s[:cut],s[cut:-1]+(s[-1]-1,)
        xs=[T.value(g+b*n) for n in range(1,6)]
        if E.check(parent,xs,3):counts['pass']+=1
        else:
            counts['fail']+=1
            failed.append(dict(sequence=s,parent=parent,terms=xs))
        if i%2000==0:print(i,dict(counts),flush=True)
    (HERE/'token-tree-calibration.json').write_text(json.dumps(dict(counts=counts,failed=failed),ensure_ascii=False,indent=2)+'\n')
    print('FINAL',dict(counts),flush=True)


if __name__=='__main__':main()
