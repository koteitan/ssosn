import sys,json,collections
from pathlib import Path
sys.path[:0]=[str(Path(__file__).resolve().parent),str(Path(__file__).resolve().parent.parent)]
import harness,std

def A(k):return (0,1,2)+(0,2)*k
W=A(0)+(1,)
def seq(ts):
 s=(0,0,2,1)
 for t in ts:s+=W if t=='W' else A(int(t[1:]))+((1,) if t[0]=='E' else ())
 return s

def main():
 frontier=[()];cases=[];counts=collections.Counter()
 for depth in range(int(sys.argv[1])):
  new=[]
  for ts in frontier:
   for t in ['A0','A1','A2','E1','W']:
    u=ts+(t,);s=seq(u)
    if s>=(0,0,2,1,0,2) or not std.is_standard(s):continue
    new.append(u)
    if t not in ['A1','A2']:continue
    k=int(t[1:]);target=harness.fs(s,2);solutions=[]
    for q in range(len(u)):
     T=u[q:-1]
     for c in range(1,len(u)+2):
      pred=seq(u[:-1]+('A'+str(k-1),)+('W',)*c+T+('A'+str(k-1),))+(0,1)
      if target==pred:solutions.append((q,c))
    cases.append(dict(tokens=u,solutions=solutions));counts[str(solutions and solutions[0][1])]+=1
  frontier=new;print(depth+1,len(new),dict(counts),flush=True)
 Path('work/law-a-explore.json').write_text(json.dumps(cases,indent=2)+'\n')
 print('NO SOLUTION',sum(not c['solutions'] for c in cases))
 for c in cases[:100]:print(c)
if __name__=='__main__':main()
