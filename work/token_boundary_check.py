"""Validate the fresh-tail laws above 002102; leading W/D are excluded."""
import argparse
import collections
import csv
import gzip
import json
from pathlib import Path

import harness
import std
import token_boundary as B
import token_value as V
import evalord as E
from ordinal import cmp
from token_targets import pretty

HERE = Path(__file__).resolve().parent
ALPHABET = ('A0', 'A1', 'A2', 'E1', 'W', 'D')


def raw(tokens):
    return sum(((0,2) if t=='D' else V.W if t=='W' else
                V.A(int(t[1:])) + ((1,) if t.startswith('E') else ()) for t in tokens), ())


def seq(tokens):
    return (0,0)+B.BASE+raw(tokens)


def admissible(tokens):
    if not tokens or tokens[0] in ('D','W'):
        return False
    for i, token in enumerate(tokens):
        if token=='D' and (i==0 or tokens[i-1]!='W'):
            return False
        if token=='W' and i and tokens[i-1]=='D':
            return False
    return B.parse(raw(tokens)) == tokens


def components(tokens):
    last=tokens[-1]
    if last=='D':
        return seq(tokens[:-1]), V.W, (0,1)
    if last=='W':
        cut=len(tokens)-2
        while tokens[cut] in ('W','D'):
            cut-=1
        return seq(tokens[:-1]), raw(tokens[cut:-1]), V.A(0)+(0,)
    if last.startswith('E'):
        return seq(tokens[:-1]+('A'+last[1:],)), (0,2), (0,)
    k=int(last[1:])
    if k==0:
        return seq(tokens[:-1])+(0,1,1), (1,), ()
    cut=0
    copies=('W','D')
    i=0
    while i<len(tokens)-1:
        atom=tokens[i]
        start=i+1
        i=start
        while i<len(tokens)-1 and tokens[i] in ('W','D'):
            i+=1
        if atom.startswith('A') and int(atom[1:])<k and i>start:
            cut=i
            copies=tokens[start:i]
    r,t=tokens[:cut],tokens[cut:-1]
    lower=('A'+str(k-1),)
    return seq(r+t+lower),raw(copies+t+lower),(0,1)


def main():
    V.BOUNDARY_EXPERIMENT=True
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('N',type=int,nargs='?',default=7)
    args=ap.parse_args()
    frontier=[()]
    counts=collections.Counter()
    failures=[]
    unknown=[]
    values={}
    rows=[]
    for size in range(1,args.N+1):
        new=[]
        for prefix in frontier:
            for atom in ALPHABET:
                tokens=prefix+(atom,)
                if not admissible(tokens):continue
                s=seq(tokens)
                if not std.is_standard(s):continue
                new.append(tokens)
                rows.append(dict(sequence=''.join(map(str,s)),tokens=tokens))
                cut=harness.Seq(s,'new').cut()
                g,d=s[:cut],s[cut:-1]+(s[-1]-1,)
                h,q,v=components(tokens)
                if g+d==h+v and v+d==q+v:
                    counts['all_n_word_certificate']+=1
                else:
                    failures.append(dict(kind='law',tokens=tokens,actual=(g,d),predicted=(h,q,v)))
                try:
                    parent=V.value(s)
                    values[s]=parent
                    xs=[]
                    for n in range(1,6):
                        term=g+d*n
                        x=V.value(term)
                        xs.append(x)
                        values[term]=x
                    if all(cmp(x,parent)<0 for x in xs) and all(cmp(a,b)<0 for a,b in zip(xs,xs[1:])):
                        counts['local_pass']+=1
                    else:failures.append(dict(kind='local_order',tokens=tokens,parent=parent,terms=xs))
                    if E.check(parent,xs,3):counts['finite_calibration_pass']+=1
                    else:failures.append(dict(kind='finite_calibration',tokens=tokens,parent=parent,terms=xs))
                except V.Unknown as exc:
                    unknown.append(dict(tokens=tokens,reason=str(exc)))
        frontier=new
        print(size,'standard',len(new),dict(counts),'fail',len(failures),'unknown',len(unknown),flush=True)
    ordered=sorted(values)
    violations=[dict(left=a,right=b,left_value=values[a],right_value=values[b])
                for a,b in zip(ordered,ordered[1:]) if cmp(values[a],values[b])>=0]
    report=dict(N=args.N,alphabet=ALPHABET,scope='fresh tails only; no leading W/D or W immediately after D',
                counts=counts,failures=failures,unresolved=unknown,rows=rows,
                valued_sequences=len(values),adjacent_violations=violations)
    (HERE/'token-boundary-check.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    with gzip.open(HERE/'token-boundary-values.tsv.gz','wt') as stream:
        wr=csv.writer(stream,delimiter='\t');wr.writerow(['sequence','value'])
        for s in ordered:wr.writerow([''.join(map(str,s)),pretty(values[s])])
    print('FINAL',dict(counts),'failures',len(failures),'unknown',len(unknown),'values',len(values),'order',len(violations))


if __name__=='__main__':main()
