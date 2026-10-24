"""Direct measurements around the three historical failures; no rule edits."""
import json
from pathlib import Path
import harness
import std
import token_tree as T
from above_p_data26 import raw,HERE
from ordinal import cmp
from token_targets import pretty


def main():
    S=('D','W','A2','A1')
    B=('D','W','A2','A0','W','D','W','A2','A0')
    C=B[:-1]+('A1',)
    targets={'historical828':('D','W','A0','W','D','W'),
             'historical27':('D','W','A1'),'historical92':S}
    report=dict(B=B,C=C,S=S,raw_order_B_C_S=raw(B)<raw(C)<raw(S),
                standard={name:std.is_standard(raw(word)) for name,word in [('B',B),('C',C),('S',S)]},
                C_ceil_is_S=std.ceil(raw(C))==raw(S),variants={})
    for variant in ('cut','movable','general'):
        T.CUT_COPY_ACTION_EXPERIMENT=variant=='cut'
        T.GENERAL_COPY_EXPERIMENT=variant in ('movable','general')
        T.MOVABLE_ONE_EXPERIMENT=variant=='movable'
        T.value_tree.cache_clear();T.body_tree.cache_clear();T.block_tree.cache_clear()
        def probe(sequence):
            try:return dict(value=pretty(T.value(sequence)),ordinal=T.value(sequence))
            except T.Unknown as error:return dict(unknown=str(error),ordinal=None)
        result={}
        for name,word in targets.items():
            sequence=raw(word);parent=probe(sequence)
            entry=dict(tokens=word,raw=sequence,standard=std.is_standard(sequence),**parent,terms=[])
            for n in range(1,6):
                term=harness.fs(sequence,n);value=probe(term)
                item=dict(n=n,raw=term,standard=std.is_standard(term),**value)
                if parent['ordinal'] is not None and value['ordinal'] is not None:
                    item['vs_parent']=cmp(value['ordinal'],parent['ordinal'])
                entry['terms'].append(item)
            result[name]=entry
        values={name:probe(raw(word)) for name,word in [('B',B),('C',C),('S',S)]}
        result['local92']=dict(values=values,B_vs_S=cmp(values['B']['ordinal'],values['S']['ordinal']),
                               C_vs_S=cmp(values['C']['ordinal'],values['S']['ordinal']))
        origin=T.Origin('measurement of existing seed functions')
        copies=T.fresh_copy_from_cut(('D','W','A2'),2)
        result['seed_functions']=dict(actual_copy=copies,
            depth1_plus1=pretty(T.ordinal(T.plus(T.typed_copy_rank(copies,1,origin),T.one(origin),origin))),
            depth0_plus1=pretty(T.ordinal(T.plus(T.typed_copy_rank(copies,0,origin),T.one(origin),origin))))
        report['variants'][variant]=result
        print(variant,'local92',{k:v['value'] for k,v in values.items()},
              'historical terms', {name:[t.get('vs_parent') for t in result[name]['terms']] for name in targets},flush=True)
    (HERE/'value-new26-focus.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')


if __name__=='__main__':main()
