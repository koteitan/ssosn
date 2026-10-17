"""Give each requested target its own bounded warm_frontier budget."""
import argparse,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--state',type=Path,required=True)
 ap.add_argument('--ext121e',action='store_true')
 ap.add_argument('--seed-noregion',type=Path)
 ap.add_argument('--seconds',type=float,default=60)
 args=ap.parse_args()
 subjects=[('a','002101210120201210121'),('b','002101210120202'),('S','002101210120210121012021'),('WW','002101210121'),('top','002102')]
 if args.ext121e:subjects=subjects[2:]
 records=[]
 for name,text in subjects:
  suffix='-e' if args.ext121e else ''
  output=HERE/f'rellift-trial-{name}{suffix}.json'
  cmd=[sys.executable,'-u',str(HERE/'noregion.py'),'--state',str(args.state),'--results',str(output),'--rellift','--roots','--seconds',str(args.seconds),'--focus',text]
  if args.ext121e:cmd+=['--ext121e']
  if args.seed_noregion:cmd+=['--seed-noregion',str(args.seed_noregion)]
  print('START',name,'budget',args.seconds,flush=True)
  run=subprocess.run(cmd,timeout=args.seconds+90)
  assert run.returncode==0,(name,run.returncode)
  report=json.loads(output.read_text())
  value=next((r['ordinal'] for r in report['three_roots'] if r['sequence']==text),None)
  if name in ('a','b'):value=next(r['ordinal'] for r in report['rows'] if r['sequence']==text)
  records.append(dict(target=name,sequence=text,budget=args.seconds,ordinal=value,resolved=report['resolved'],unresolved=report['unresolved'],total_jobs=report['total_jobs'],total_seconds=report['total_seconds']))
  manifest=HERE/('rellift-trials-e.json' if args.ext121e else 'rellift-trials.json')
  manifest.write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
  final=HERE/('rellift-roots-on.json' if args.ext121e else 'rellift-results.json')
  final.write_text(output.read_text())
  final.with_suffix('.tsv').write_text(output.with_suffix('.tsv').read_text())
  print('DONE',name,'known',value is not None,flush=True)

if __name__=='__main__':main()
