"""Audit the extended evaluator, including explicit built-in-base checks."""
import collections
import csv
import gzip
import json
from pathlib import Path

import harness
import std
import evalord as E
import token_base2 as B
import token_laws as L
import token_value as V
from ordinal import cmp
from token_targets import pretty

HERE = Path(__file__).resolve().parent


def target_checks():
    rows=[]
    for text in ['0021021','00211','0022','003']:
        s=tuple(map(int,text))
        cut=harness.Seq(s,'new').cut()
        g,b=s[:cut],s[cut:-1]+(s[-1]-1,)
        row=dict(sequence=text,standard=std.is_standard(s),G=g,B=b,terms=[])
        try:row.update(status='value',ordinal=V.value(s))
        except V.Unknown as exc:row.update(status='unresolved',reason=str(exc))
        for n in range(1,6):
            t=harness.fs(s,n)
            term=dict(n=n,sequence=''.join(map(str,t)),law_matches=t==g+b*n)
            try:
                x=V.value(t)
                term.update(status='value',ordinal=x,rendered=pretty(x))
            except V.Unknown as exc:term.update(status='unresolved',reason=str(exc))
            row['terms'].append(term)
        rows.append(row)
    (HERE/'token-extension-targets.json').write_text(json.dumps(dict(cases=rows),ensure_ascii=False,indent=2)+'\n')


def main():
    target_checks()
    builtin = []
    for j in range(1, 9):
        s = (0, 0, 2, 1) + V.W * j
        parent = V.value(s)
        terms = []
        for n in range(1, 6):
            t = harness.fs(s, n)
            x = V.value(t)
            terms.append(dict(n=n, sequence=''.join(map(str,t)), ordinal=x, rendered=pretty(x),
                              law_matches=t == L.expected(('W',)*j, n)))
        builtin.append(dict(name='W^'+str(j), sequence=s, ordinal=parent,
                            rendered=pretty(parent), terms=terms,
                            local_pass=all(cmp(t['ordinal'],parent)<0 for t in terms)
                            and all(cmp(a['ordinal'],b['ordinal'])<0 for a,b in zip(terms,terms[1:])),
                            finite_calibration=E.check(parent,[t['ordinal'] for t in terms],3)))
    s=(0,0,2,1,0,2)
    parent=V.value(s)
    terms=[]
    for n in range(1,6):
        t=harness.fs(s,n)
        x=V.value(t)
        terms.append(dict(n=n,sequence=''.join(map(str,t)),ordinal=x,rendered=pretty(x),
                          law_matches=t==(0,0,2,1)+V.W*(n-1)+(0,1)))
    builtin.append(dict(name='002102',sequence=s,ordinal=parent,rendered=pretty(parent),terms=terms,
                        local_pass=all(cmp(t['ordinal'],parent)<0 for t in terms)
                        and all(cmp(a['ordinal'],b['ordinal'])<0 for a,b in zip(terms,terms[1:])),
                        finite_calibration=E.check(parent,[t['ordinal'] for t in terms],3)))

    boundary=(0,0,2,1,0,2)
    bases=[boundary,boundary+V.A(1),boundary+V.A(0)+V.W+(0,2)]
    core=json.loads((HERE/'token-laws-check.json').read_text())
    bases += [tuple(map(int,r['sequence'])) for r in core['rows'] if len(r['tokens'])<=5]
    # Include the binary family, without depending on temporary reference states.
    import itertools
    for size in range(9):
        for bits in itertools.product((0,1),repeat=size):
            s=(0,0,2)+B.emit(bits)
            if std.is_standard(s):bases.append(s)
    tails=[]
    for m in range(5):tails.append(V.A(0)+V.W*m)
    tails += [(V.A(0)+V.W)*2, V.A(0)+V.W*2+V.A(0)+V.W, V.A(0)*3]
    tails += [V.A(0)+V.W+(0,2), (V.A(0)+V.W+(0,2))*2,
              V.A(0)+V.W+(0,2)+V.A(0)]
    relative_counts=collections.Counter()
    relative_fail=[]
    values={}
    for base in sorted(set(bases)):
        for tail in tails:
            s=base+tail
            if not std.is_standard(s):continue
            parent=V.value(s)
            values[s]=parent
            if s[-2:]==(0,2):
                h,q,v=s[:-2],V.W,(0,1)
            elif s[-4:]==V.W:
                rest=s[:-4]
                m=0
                while rest[-4:]==V.W:rest=rest[:-4];m+=1
                h,q,v=s[:-4],V.A(0)+V.W*m,V.A(0)+(0,)
            else:
                h,q,v=s[:-3]+(0,1,1),(1,),()
            cut=harness.Seq(s,'new').cut()
            g,d=s[:cut],s[cut:-1]+(s[-1]-1,)
            if g+d==h+v and v+d==q+v:relative_counts['all_n_word_certificate']+=1
            else:relative_fail.append(dict(sequence=s,kind='law',actual=(g,d),predicted=(h,q,v)))
            xs=[]
            for n in range(1,6):
                t=harness.fs(s,n)
                x=V.value(t)
                xs.append(x)
                values[t]=x
            if all(cmp(x,parent)<0 for x in xs) and all(cmp(a,b)<0 for a,b in zip(xs,xs[1:])):
                relative_counts['local_pass']+=1
            else:relative_fail.append(dict(sequence=s,parent=parent,terms=xs))
    print('relative',dict(relative_counts),'fail',len(relative_fail),flush=True)

    closed_rules=[]
    for tokens in [('A1',),('A0','W','D')]:
        from token_boundary_check import seq,components
        s=seq(tokens)
        parent=V.value(s)
        h,q,v=components(tokens)
        cut=harness.Seq(s,'new').cut()
        g,d=s[:cut],s[cut:-1]+(s[-1]-1,)
        terms=[]
        for n in range(1,6):
            t=g+d*n;x=V.value(t)
            values[t]=x
            terms.append(dict(n=n,sequence=''.join(map(str,t)),ordinal=x,rendered=pretty(x)))
        values[s]=parent
        closed_rules.append(dict(sequence=s,tokens=tokens,ordinal=parent,rendered=pretty(parent),
                                 all_n_word_certificate=(g+d==h+v and v+d==q+v),terms=terms,
                                 local_pass=all(cmp(t['ordinal'],parent)<0 for t in terms)
                                 and all(cmp(a['ordinal'],b['ordinal'])<0 for a,b in zip(terms,terms[1:])),
                                 finite_calibration=E.check(parent,[t['ordinal'] for t in terms],3)))

    coverage=[]
    unsupported=collections.Counter()
    examples={}
    for root,maxlen in [((0,0,2,1,0,2),24),((0,0,3),20)]:
        closure=harness.closure([root],nmax=3,maxlen=maxlen)
        counts=collections.Counter()
        new_range=collections.Counter()
        for s in sorted(closure):
            if len(s)<2 or s[:2]!=(0,0):continue
            counts['inputs']+=1
            try:
                x=V.value(s)
                values[s]=x
                tag='resolved'
            except V.Unknown as exc:
                tag='unresolved'
                reason=str(exc)
                unsupported[reason]+=1
                examples.setdefault(reason,''.join(map(str,s)))
            counts[tag]+=1
            if (0,0,2,1,0,2)<=s<(0,0,3):new_range[tag]+=1
        coverage.append(dict(root=root,maxlen=maxlen,nmax=3,total_closure=len(closure),counts=counts,
                             new_range=new_range))
        print('closure',root,counts,'new range',new_range,flush=True)
    ordered=sorted(values)
    violations=[dict(left=a,right=b,left_value=values[a],right_value=values[b])
                for a,b in zip(ordered,ordered[1:]) if cmp(values[a],values[b])>=0]
    # Explicitly check standard membership of every resolved input in the new range.
    new_standard=[s for s in ordered if (0,0,2,1,0,2)<=s<(0,0,3) and std.is_standard(s)]
    new_violations=[dict(left=a,right=b) for a,b in zip(new_standard,new_standard[1:])
                    if cmp(values[a],values[b])>=0]
    with gzip.open(HERE/'token-extension-values.tsv.gz','wt') as stream:
        wr=csv.writer(stream,delimiter='\t');wr.writerow(['sequence','value'])
        for s in ordered:wr.writerow([''.join(map(str,s)),pretty(values[s])])
    report=dict(builtin_checks=builtin,closed_rule_checks=closed_rules,relative_counts=relative_counts,relative_failures=relative_fail,
                coverage=coverage,unsupported=[dict(reason=r,count=n,example=examples[r])
                                               for r,n in unsupported.most_common()],
                valued_sequences=len(values),adjacent_violations=violations,
                verified_new_range_standard=len(new_standard),new_range_adjacent_violations=new_violations)
    (HERE/'token-extension-check.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print('FINAL values',len(values),'order',len(violations),'verified new range',len(new_standard),
          'order',len(new_violations),flush=True)


if __name__=='__main__':main()
