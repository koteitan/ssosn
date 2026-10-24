"""Value-free relative-tail tests: enumeration and cofinal-copy obstruction.

timeout 600 python3 work/reltail30_check.py --N 6
No candidate ordinal evaluator is called. The counterexample concerns a COMMON
map Y(T) at depth zero; it does not refute context-dependent maps Y_X(T).
"""
import argparse
from functools import lru_cache
import gzip
import itertools
import json
import time

import harness
import std
import tree
import shape
from above_p_data26 import HERE,raw

ALPHABET=('A0','A1','A2','W','D')
BASES=(('DW_A0',('D','W','A0'),0),('DD_A0',('D','D','A0'),0),
       ('DDD_A0',('D','D','D','A0'),0),('DDD_A1',('D','D','D','A1'),1))


def shifted(tokens,depth):
    return tuple('A'+str(int(t[1:])+depth) if t.startswith('A') else t for t in tokens)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--N',type=int,default=6)
    args=parser.parse_args()
    start=time.monotonic()
    cls=harness.Seq;original=cls.cut
    @lru_cache(maxsize=32768)
    def cut(s,mode):return original(cls(s,mode))
    cls.cut=lambda self:cut(self.S,self.mode)
    @lru_cache(maxsize=100000)
    def standard(s):return std.is_standard(s)
    rows=[];levels=[];previous=[{()} for _ in BASES];seen=[set() for _ in BASES]
    first_difference=None
    for n in range(args.N+1):
        current=[set() for _ in BASES];counts=[0]*len(BASES)
        for word in itertools.product(ALPHABET,repeat=n):
            flags=[]
            for j,(name,base,depth) in enumerate(BASES):
                s=raw(base+shifted(word,depth))
                good=(not word or word[:-1] in previous[j]) and standard(s)
                flags.append(good)
                if good:
                    counts[j]+=1;current[j].add(word);seen[j].add(s)
            rows.append(dict(tail=word,standard=flags))
            if first_difference is None and len(set(flags[:3]))>1:
                first_difference=dict(tail=word,standard=flags)
        levels.append(dict(length=n,words=5**n,standard=counts))
        previous=current
        print(levels[-1],flush=True)
    binary=[];binary_checked=0
    for n in range(13):
        for y in itertools.product((0,1),repeat=n):
            oracle=standard((0,0)+y);syntactic=shape.shape(tree.parse(y))
            assert oracle==syntactic,y
            binary_checked+=1
            if oracle:binary.append(y)
    A=BASES[0][1];B=BASES[1][1];Q=('W','D','W','A0');L=('W','D','W','A1')
    parents={'AD':A+('D',),'BL':B+L,'BD':B+('D',)}
    certs={}
    for name,word in parents.items():
        s=raw(word)
        assert standard(s)
        c=harness.Seq(s,'new').cut();g=s[:c];repeat=s[c:-1]+(s[-1]-1,)
        if name in ('AD','BL'):
            head=raw(A if name=='AD' else B+Q);q=raw(Q)[4:];v=(0,1)
            assert g+repeat==head+v and v+repeat==q+v
            certs[name]=dict(sequence=s,standard=True,cut=c,G=g,B=repeat,H=head,Q=q,V=v,
                all_n_word_identities=True)
        else:certs[name]=dict(sequence=s,standard=True)
    tests=[]
    for n in range(0,33):
        qa=raw(A+Q*n);qb=raw(B+Q*n)
        assert standard(qa) and standard(qb)
        assert qb<raw(B+L)<raw(B+('D',))
        assert harness.fs(raw(A+('D',)),n+1)==qa+(0,1)
        if n:assert harness.fs(raw(B+L),n)==qb+(0,1)
        tests.append(dict(n=n,A_standard=True,B_standard=True))
    # The literal fs is not closed in the token alphabet, even for A0.
    literal=harness.fs(raw(A+('A0',)),1)
    data=dict(max_tail_tokens=args.N,alphabet=ALPHABET,bases=BASES,levels=levels,rows=rows,
        raw_unique_standard=[len(s) for s in seen],
        first_admissibility_difference=first_difference,binary_max_tail_length=12,
        binary_checked=binary_checked,binary_standard_count=len(binary),binary_standard=sorted(binary),
        cofinal_counterexample=dict(A=A,B=B,Q=Q,L=L,parents=certs,tests=tests,
            BL_less_BD=raw(B+L)<raw(B+('D',)),
            statement='No common base-independent Y(T) preserving both order and cofinal expansions',
            scope='Does not rule out context-dependent Y_X(T) or a different induced expansion'),
        literal_A0_expansion=dict(parent=raw(A+('A0',)),term1=literal),
        seconds=time.monotonic()-start)
    with gzip.open(HERE/'reltail30-data.json.gz','wt') as target:json.dump(data,target,ensure_ascii=False,separators=(',',':'))
    (HERE/'reltail30-counterexample.json').write_text(json.dumps(data['cofinal_counterexample'],ensure_ascii=False,indent=2)+'\n')
    print('FINISHED','unique standard',data['raw_unique_standard'],'binary standard',len(binary),
          'first difference',first_difference,'seconds',round(data['seconds'],2),flush=True)


if __name__=='__main__':main()
