"""Explore relative-lift boundaries using only the frozen NOREGION state."""
import sys,pickle,json,collections
from pathlib import Path
sys.path[:0]=[str(Path(__file__).resolve().parent),str(Path(__file__).resolve().parent.parent)]
import lift,conj,rule6
from ordinal import ONE,P,add,cmp,w,nat,ZERO
from order_region import pretty,tu

def main():
 with open(sys.argv[1],'rb') as f:state=pickle.load(f)
 assert state['signature'][0]=='noregion-no-II-v1'
 r=json.load(open('work/noregion-results.json'))
 cases=[]
 for row in r['rows']:
  if row['ordinal'] is None:continue
  s=tuple(map(int,row['sequence']));actual=tu(row['ordinal'])
  for cut in range(4,len(s)):
   base=s[:cut];x=state['memo'].get(base) or state['hmemo'].get(base[2:])
   if x is None or len(x)!=1 or x[0][1]!=ONE:continue
   y=lift.unlift((2,1)+s[cut:])
   if y is None:continue
   v=conj.v(y);prediction=P(ONE,add(x[0][2],v))
   cases.append(dict(sequence=row['sequence'],base=''.join(map(str,base)),Y=''.join(map(str,y)),v=v,index=x[0][2],bound=cmp(v,w(nat(2)))<0,agree=prediction==actual,prediction=prediction,actual=actual))
 for name,filtered in [('all',cases),('lessw2',[c for c in cases if c['bound']]),('lastA1orW',[c for c in cases if c['bound'] and (c['base'].endswith('01202') or c['base'].endswith('0121'))])]:
  print(name,len(filtered),'agree',sum(c['agree'] for c in filtered))
  for c in [c for c in filtered if not c['agree']][:12]:print('DIFF',c['base'],c['Y'],pretty(c['prediction']),pretty(c['actual']))
 out=Path('work/rellift-explore.json');out.write_text(json.dumps(cases,ensure_ascii=False,indent=2)+'\n')
 for c in cases:
  if c['bound'] and c['base'].endswith('0121'):
   print('Wbase',c['base'],pretty(c['index']),c['Y'],c['agree'])
if __name__=='__main__':main()
