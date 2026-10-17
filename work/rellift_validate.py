"""Compare RELLIFT with frozen, independent NOREGION block values."""
import argparse,csv,gzip,json,pickle,signal,sys
from functools import lru_cache
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import rule6,lift,conj,std
from ordinal import ONE,P,add,cmp,w,nat
from order_region import pretty,tu
class Timeout(Exception):pass
def alarm(*_):raise Timeout

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--state',type=Path,required=True)
 ap.add_argument('--out',type=Path,default=HERE/'rellift-validation.json')
 args=ap.parse_args()
 with args.state.open('rb') as f:state=pickle.load(f)
 assert state['signature'][0]=='noregion-no-II-v1'
 rule6.memo,rule6.hmemo=state['memo'].copy(),state['hmemo'].copy()
 rule6.NOREGION=rule6.RELLIFT=rule6.EXT=rule6.MORE=rule6.USE_LIFT=True
 rule6.EXT121=rule6.EXT121E=False
 rule6.is_selfref=lru_cache(maxsize=200000)(rule6.is_selfref)
 rule6.lower.lower=lambda u:None
 signal.signal(signal.SIGALRM,alarm)
 evaluation=json.load(open(HERE/'noregion-results.json'))
 cases=[];predictions={};reasons={}
 p=rule6.NO_REGION_PREFIX
 known={u:x for u,x in state['hmemo'].items()
        if u[:len(p)]==p or rule6.relative_parts(u) is not None}
 for row in evaluation['rows']:
  if row['ordinal'] is not None:
   u=tuple(map(int,row['sequence']))[2:]
   if rule6.is_selfref(u):known[u]=tu(row['ordinal'])
 for u,x in sorted(known.items()):
  parts=rule6.relative_parts(u)
  if parts is None:continue
  base,m,n=parts
  # Do not warm unknown bases while checking the independent reference data.
  bv=state['hmemo'].get(base)
  if bv is None or len(bv)!=1 or bv[0][1]!=ONE:
   cases.append(dict(sequence='00'+''.join(map(str,u)),status='unresolved',reference=x,reason='base unknown'));continue
  rule6.st.update(depth=0,taint=0)
  signal.setitimer(signal.ITIMER_REAL,.02)
  try:
   y=rule6.rules(u)
   status=('agree' if y==x else 'differ') if y is not None and not rule6.st['taint'] else 'unresolved'
  except (Timeout,RecursionError):y=None;status='unresolved'
  finally:signal.setitimer(signal.ITIMER_REAL,0)
  item=dict(sequence='00'+''.join(map(str,u)),base='00'+''.join(map(str,base)),m=m,n=n,status=status,prediction=y,reference=x)
  cases.append(item)
  if y is not None and status!='unresolved':predictions[(0,0)+u]=y
 # Union of independent R/hook values and rule predictions. A zero audit on
 # this superset implies zero on its standard subset, without importing old values.
 union={s:{'R':x} for s,x in state['memo'].items() if s[2:2+len(p)]==p}
 for u,x in known.items():
  if u[:len(p)]==p:union.setdefault((0,0)+u,{})['hook']=x
 for s,x in predictions.items():
  if s[2:2+len(p)]==p:union.setdefault(s,{})['RELLIFT']=x
 ordered=sorted(union);bad=[];conflicts=[]
 for s,vs in union.items():
  if len(set(vs.values()))>1:conflicts.append(''.join(map(str,s)))
 from evalord import _Key
 for a,b in zip(ordered,ordered[1:]):
  av=max(union[a].values(),key=_Key);bv=min(union[b].values(),key=_Key)
  if cmp(av,bv)>=0:bad.append(dict(left=''.join(map(str,a)),right=''.join(map(str,b)),left_value=av,right_value=bv))
 ys=sorted({tuple(t['binary']) for t in json.load(open(HERE/'noregion-patterns.json'))['agree']},key=lambda x:(len(x),x))
 boundaries=[]
 bases=[(2,1,0,1,2,1)]+[(2,1,0,1,2,1)+(0,1,2,0,2)*k for k in range(1,6)]
 for base in bases:
  bv=state['hmemo'].get(base)
  if bv is None:continue
  for y in [(),(0,)*8,(1,0,0,1),(1,0,1),(1,1)]:
   u=base+lift.lift(y)[2:];actual=state['hmemo'].get(u) or state['memo'].get((0,0)+u)
   prediction=P(ONE,add(bv[0][2],conj.v(y)))
   boundaries.append(dict(base='00'+''.join(map(str,base)),Y=y,v=conj.v(y),standard=std.is_standard((0,0)+u),within_bound=cmp(conj.v(y),w(nat(2)))<0,prediction=prediction,reference=actual,status='unresolved' if actual is None else 'agree' if prediction==actual else 'differ',rule_parts=rule6.relative_parts(u)))
 case_by_sequence={c['sequence']:c for c in cases}
 core=[]
 for row in evaluation['rows']:
  c=case_by_sequence.get(row['sequence'])
  parts=rule6.relative_parts(tuple(map(int,row['sequence']))[2:])
  status=c['status'] if c else 'rule not applicable' if parts is None else 'reference unresolved' if row['ordinal'] is None else 'base unresolved'
  core.append(dict(sequence=row['sequence'],status=status))
 report=dict(method='frozen NOREGION reference; no old values; per comparison 0.02 seconds',counts={k:sum(c['status']==k for c in cases) for k in ['agree','differ','unresolved']},known_blocks=len(known),cases=[c for c in cases if c['status']!='agree'],core=core,checked_Y=ys,checked_Y_pairs=sorted({(c['m'],c['n']) for c in cases if 'm' in c}),checked_bases=len({c['base'] for c in cases if 'base' in c}),boundaries=boundaries,audit=dict(checked_sequences=len(ordered),standard_membership_filtered=False,adjacent_violations=bad,same_sequence_conflicts=conflicts))
 args.out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
 with gzip.open(args.out.with_suffix('.tsv.gz'),'wt') as f:
  wr=csv.writer(f,delimiter='\t');wr.writerow(('sequence','base','m','n','status','prediction','reference'))
  for c in cases:wr.writerow((c['sequence'],c.get('base',''),c.get('m',''),c.get('n',''),c['status'],pretty(c['prediction']) if c.get('prediction') is not None else '',pretty(c['reference'])))
 print(report['counts'],'audit',len(ordered),'violations',len(bad),'conflicts',len(conflicts),flush=True)
 print('boundary',[(c['base'],c['Y'],c['status']) for c in boundaries],flush=True)
if __name__=='__main__':main()
