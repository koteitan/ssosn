"""Definition-derived suffix-parent tree and record-maximum cut.

No Seq, fs, token law, ordinal evaluator, or standardness oracle is imported.
Positions are 1-based; rank[L+1] is the empty suffix rank.
"""
from dataclasses import dataclass

@dataclass
class CutTree:
    sequence: tuple
    suffix_rank: tuple
    parent: tuple
    record: tuple

    @classmethod
    def build(cls, sequence):
        s=tuple(sequence);length=len(s)
        # Lexicographic ranks of the empty suffix and every nonempty suffix.
        order=sorted(range(1,length+2),key=lambda p:s[p-1:])
        rank=[0]*(length+2)
        for r,p in enumerate(order):rank[p]=r
        parent=[1]*(length+1);stack=[]
        for p in range(1,length+1):
            while stack and rank[stack[-1]]>=rank[p]:stack.pop()
            parent[p]=stack[-1] if stack else 1
            stack.append(p)
        record=[length]*(length+1)
        if s:
            best=length
            for p in range(length-1,0,-1):
                if s[p-1]<s[-1] and rank[p+1]>rank[best+1]:best=p
                record[p]=best
        return cls(s,tuple(rank),tuple(parent),tuple(record))

    def ancestors(self):
        p=len(self.sequence)
        while True:
            p=self.parent[p]
            yield p

    def locate(self):
        """First record plateau or low-label witness along the parent path."""
        s=self.sequence;length=len(s)
        if length<2:raise ValueError('length >= 2 required')
        path=self.ancestors();previous=next(path);chain=[previous];records=[self.record[previous]]
        for depth in range(2,length+1):
            p=next(path);m=self.record[p];chain.append(p);records.append(m)
            plateau=m==records[-2]
            witness=next((j for j in range(p+1,m+1) if s[j-1]<=s[p-1]),None)
            if plateau or witness is not None:
                return dict(br=depth,cut=m,parents=chain,records=records,
                            reason='record_plateau' if plateau else 'low_label_witness',witness=witness)
        return dict(br=length,cut=records[-1],parents=chain,records=records,reason='length_fallback',witness=None)

    def repeat(self,n):
        if self.sequence[-1]==0:
            raise ValueError('successor expansion drops the last zero instead')
        c=self.locate()['cut'];s=self.sequence
        return s[:c]+(s[c:-1]+(s[-1]-1,))*n
