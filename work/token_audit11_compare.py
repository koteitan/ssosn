"""Recheck every exact reference row in the section 11 standard-set export."""
import argparse,collections,csv,gzip,json,pickle,sys,time
from pathlib import Path
from functools import lru_cache
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import token_value as V
from ordinal import cmp,show
fmt=lru_cache(maxsize=100000)(show)
def tu(x):return tuple(tu(v) for v in x) if isinstance(x,list) else x

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--seed',type=Path,required=True);args=ap.parse_args()
 with args.seed.open('rb') as f:state=pickle.load(f)
 supplemental={};report=json.loads((HERE/'order-region-all.json').read_text())
 for row in report['comparisons']:
  for source in ['rule','real_sup']:
   x=row[source]
   if x['status']=='clean':supplemental[(row['sequence'],source)]=tu(x['ordinal'])
 for row in report['focused']:
  for term in row['terms']:
   if term['status']=='clean':supplemental[(term['sequence'],'focused_term')]=tu(term['ordinal'])
 for filename in ['ext121-independent-checked.json','ext121e-independent-checked.json']:
  data=json.loads((HERE/filename).read_text())
  for row in data['cases']:
   for field in ['off_real_sup','off_rule_after_warm','off_rule']:
    x=row.get(field,{})
    if x.get('status')=='clean':supplemental[(row['sequence'],filename+':'+field)]=tu(x['ordinal'])
   if filename.startswith('ext121e') and row['on_rule']['status']=='clean':supplemental[(row['sequence'],'published_rule_EXT121E')]=tu(row['on_rule']['ordinal'])
 data=json.loads((HERE/'ext121e-roots-on.json').read_text())
 for row in data['rows']:
  if row['status']=='clean':supplemental[(row['sequence'],'published_evaluator_EXT121E')]=tu(row['ordinal'])
 counts=collections.Counter();sources={};refs={};values={};started=time.monotonic()
 with gzip.open(HERE/'order-region-all-values.tsv.gz','rt') as f,gzip.open(HERE/'token-audit11-comparison.tsv.gz','wt') as out:
  wr=csv.writer(out,delimiter='\t');wr.writerow(('sequence','source','result','reference','token_value'))
  for row in csv.DictReader(f,delimiter='\t'):
   s=tuple(map(int,row['sequence']));source=row['source']
   old=state['memo'][s] if source=='cache_R' else state['hmemo'][s[2:]] if source=='cache_hook' else supplemental[(row['sequence'],source)]
   assert fmt(old)==row['ordinal'],(row['sequence'],source,'export mismatch')
   new=V.value(s);values[s]=new;refs.setdefault(s,set()).add(old)
   status='agree' if old==new else 'differ';counts[status]+=1;sources.setdefault(source,collections.Counter())[status]+=1
   wr.writerow((row['sequence'],source,status,fmt(old) if status=='differ' else '',fmt(new) if status=='differ' else ''))
 unique=collections.Counter();sequences=collections.Counter()
 for s,rs in refs.items():
  results=[x==values[s] for x in rs]
  unique['agree']+=sum(results);unique['differ']+=len(results)-sum(results)
  sequences['all_agree' if all(results) else 'all_differ' if not any(results) else 'mixed']+=1
 ordered=sorted(values);bad=[]
 for a,b in zip(ordered,ordered[1:]):
  if cmp(values[a],values[b])>=0:bad.append(dict(left=''.join(map(str,a)),right=''.join(map(str,b))))
 result=dict(standard_sequences=len(refs),reference_rows=counts,unique_sequence_reference_pairs=unique,sequence_classes=sequences,by_source=sources,adjacent_violations=bad,all_original_rows_recovered=True,seconds=time.monotonic()-started)
 (HERE/'token-audit11-comparison.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
 print(result,flush=True)
if __name__=='__main__':main()
