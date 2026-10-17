"""Check predictions as separate candidates, without writing evaluator memos."""
import json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
from ordinal import cmp
from order_region import tu

r=json.loads((HERE/'revised-predictions.json').read_text())
evaluation=json.loads((HERE/'rellift-hint-results.json').read_text())
known=[(row['sequence'],tu(row['ordinal'])) for row in evaluation['rows'] if row['ordinal'] is not None]
candidates=[('J','00210121012020121012020121',tu(r['predicted_J'])),
            ('a','002101210120201210121',tu(r['predicted_a'])),
            ('b','002101210120202',tu(r['predicted_b'])),
            ('b A0, index +1','002101210120202012',tu(r['bA0_index_successor']))]
checks=[]
for name,s,x in candidates:
 bad=[]
 for t,y in known:
  c=cmp(x,y)
  if (t<s and c<=0) or (t>s and c>=0) or (t==s and c!=0):
   bad.append(dict(sequence=t,ordinal=y))
 checks.append(dict(name=name,sequence=s,prediction=x,known_standard_values=len(known),violations=bad))
ordered=sorted(candidates,key=lambda t:t[1])
pairs=[dict(left=a[0],right=b[0],strict=cmp(a[2],b[2])<0) for a,b in zip(ordered,ordered[1:])]
result=dict(predictions_inserted=False,known_values=len(known),checks=checks,between_predictions=pairs,
            outer_successor_conflict='b0 < b A0 are both standard; if o(b)=E, o(b0)=E+1, so o(b A0)>E+1')
(HERE/'revised-order.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print('known',len(known),'violations',[(x['name'],len(x['violations'])) for x in checks],pairs)
