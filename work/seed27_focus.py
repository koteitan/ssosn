"""Measure the consistent-seed hypothesis and exact copies at remaining failures."""
import gzip
import json
import harness
import std
import token_tree as T
from above_p_data26 import HERE,raw
from ordinal import cmp
from token_targets import pretty


def main():
    T.CUT_COPY_ACTION_EXPERIMENT=True
    T.CONSISTENT_COPY_SEED_EXPERIMENT=True
    data=json.load(gzip.open(HERE/'value-new26-seed.json.gz','rt'))
    S=('D','W','A2','A1')
    B=('D','W','A2','A0','W','D','W','A2','A0')
    C=B[:-1]+('A1',)
    targets={'S':S,'B':B,'C':C,'DDD_A1':('D','D','D','A1'),
        'DDW_A1':('D','D','W','A1'),
        'promoted_A2':('D','W','A1','W','D','W','A2'),
        'DW_A0_WDW':('D','W','A0','W','D','W'),
        'DW_A1':('D','W','A1')}
    for number,row in enumerate(data['extended_examples']['True'][:2],1):
        for side in ('lower_witness','upper_witness'):
            w=row[side]
            if w and w['tokens']:targets[f'failure{number}_{side}']=tuple(w['tokens'])
    for number,row in enumerate(data['extended_examples'].get('False',[])[:2],1):
        targets[f'missing{number}']=tuple(row['tokens'])
    rows={}
    values={}
    for name,tokens in targets.items():
        s=raw(tokens);parent=T.value(s);values[name]=parent
        row=dict(tokens=tokens,raw=s,standard=std.is_standard(s),value=pretty(parent))
        if row['standard']:
            cut=harness.Seq(s,'new').cut();g,b=s[:cut],s[cut:-1]+(s[-1]-1,)
            terminal=(0,1) if tokens[-1].startswith('A') else (0,)
            first=harness.fs(s,1)
            if first[-len(terminal):]==terminal:
                h=first[:-len(terminal)];q=(terminal+b)[:-len(terminal)]
                row['copy']=dict(cut=cut,G=g,B=b,H=T.parse(h[4:],True),Q=T.parse(q,True),
                    terminal=terminal,all_n_certificate=(g+b==h+terminal and terminal+b==q+terminal))
            row['terms']=[]
            for n in range(1,6):
                term=harness.fs(s,n);value=T.value(term)
                item=dict(n=n,raw=term,standard=std.is_standard(term),value=pretty(value),
                          vs_parent=cmp(value,parent))
                try:item['tokens']=T.parse(term[4:-len(terminal)],True);item['terminal']=terminal
                except T.Unknown:pass
                row['terms'].append(item)
        else:
            ceiling=std.ceil(s)
            row['ceiling']=dict(raw=ceiling,tokens=T.parse(ceiling[4:],True),
                standard=std.is_standard(ceiling),value=pretty(T.value(ceiling)),
                candidate_vs_ceiling=cmp(parent,T.value(ceiling)))
        rows[name]=row
    report=dict(implementation='consistent depth-zero seed for fresh roots and promotion frames',
        rows=rows,local92=dict(B_less_C_less_S=raw(B)<raw(C)<raw(S),
        B_vs_S=cmp(values['B'],values['S']),C_vs_S=cmp(values['C'],values['S']),
        C_ceil_S=std.ceil(raw(C))==raw(S)))
    (HERE/'seed27-focus.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    for name,row in rows.items():
        print(name,row['standard'],row['value'],row.get('copy'),flush=True)
        if name in ('DDD_A1','DDW_A1'):
            for term in row['terms']:print(' term',term['n'],term['value'],term['vs_parent'],flush=True)
    print('local92',report['local92'],flush=True)


if __name__=='__main__':main()
