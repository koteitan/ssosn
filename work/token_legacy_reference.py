"""Regenerate the old toksearch2 reference, in isolation from token_value."""
import argparse,collections,json,pickle,signal,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import harness,rule6,lift,std
from ordinal import cmp
class Timeout(Exception):pass
def alarm(*_):raise Timeout

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--seed',type=Path)
 ap.add_argument('--seconds',type=float,default=900);ap.add_argument('--job-seconds',type=float,default=5)
 ap.add_argument('--out',type=Path,default=HERE/'token-legacy-reference.json');args=ap.parse_args()
 rule6.USE_LIFT=rule6.EXT=rule6.MORE=True;rule6.MAXD=6
 rule6.RELLIFT=rule6.NOREGION=rule6.EXT121=rule6.EXT121E=False
 lift.unlift((2,1))
 if args.seed:
  with args.seed.open('rb') as f:seed=pickle.load(f)
  rule6.memo,rule6.hmemo=seed['memo'],seed['hmemo']
 signal.signal(signal.SIGALRM,alarm)
 TOK={'A0':(0,1,2),'A1':(0,1,2,0,2),'A2':(0,1,2,0,2,0,2),'1':(1,)}
 LO=(0,0,2,1,0,1,2,0,2,1);HI=(0,0,2,1,0,2)
 frontier=[((),(2,1))];seen=set();rows=[];unique={};started=time.monotonic();complete=True
 for depth in range(9):
  new=[]
  for tokens,u in frontier:
   for atom,tail in TOK.items():
    if atom=='1' and tokens and tokens[-1]=='1':continue
    v=u+tail;s=(0,0)+v
    if v in seen or s>=HI:continue
    seen.add(v)
    if not std.is_standard(s):continue
    ts=tokens+(atom,);new.append((ts,v))
    if s<LO:continue
    remaining=args.seconds-(time.monotonic()-started)
    if remaining<=0:complete=False;break
    signal.setitimer(signal.ITIMER_REAL,min(args.job_seconds,remaining))
    try:
     x,taint=rule6.value(s);status='clean' if x is not None and not taint else 'tainted/missing'
    except (Timeout,RecursionError):x=None;status='timeout';rule6.st['depth']=0
    finally:signal.setitimer(signal.ITIMER_REAL,0)
    row=dict(sequence=''.join(map(str,s)),tokens=ts,status=status,ordinal=x if status=='clean' else None)
    rows.append(row)
    if status=='clean' and (x not in unique or len(v)<len(unique[x]['sequence'])-2):unique[x]=row
   if not complete:break
  frontier=new
  report=dict(method='old toksearch2 flags; clean means no hypothesis II in returned value',seeded=args.seed is not None,depth=depth+1,complete=complete,seconds=time.monotonic()-started,rows=rows,unique_values=list(unique.values()))
  args.out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
  args.out.with_name('token-legacy-977.json').write_text(json.dumps(dict(
   method='regenerated distinct clean legacy values; not a recovered historical snapshot',
   complete=complete,unique_values_count=len(unique),rows=list(unique.values())),
   ensure_ascii=False,indent=2)+'\n')
  print('depth',depth+1,'rows',len(rows),'unique',len(unique),'statuses',dict(collections.Counter(r['status'] for r in rows)),flush=True)
  if not complete:break
if __name__=='__main__':main()
