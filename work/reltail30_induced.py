"""Calibrate the contracted token expansions against the actual binary fs.

No candidate token valuation is used. Binary values use the 0/1 map only.
The W/WW images are forced by successor and cofinal order structure, not ranks
in two truncated enumeration lists. A context-dependent map is allowed.
"""
import json
import harness
import std
import conj
from ordinal import OMEGA,ONE,nat,add,cmp
from above_p_data26 import HERE,raw

BASES=(('D','W','A0'),('D','D','A0'),('D','D','D','A0'))
YW=(0,0,1)
YWW=(0,0,1,0,1)


def r(k):return ('W',)+('A0','W')*k
def image_r(k):return (0,0)+(1,0,0)*k+(1,)
def image_child(n):return (0,0)+(1,0,0)*(n-1)+(1,0)


def main():
    report=dict(bases=BASES,W_image=YW,WW_image=YWW,rows=[],
        method='token fs stripped of terminal0 and base prefix; binary target is actual uncontracted fs',
        scope='exact commutation mismatch; neither a disproof of order isomorphism nor of cofinal equivalence')
    for base in BASES:
        prefix=raw(base)
        assert std.is_standard(raw(base+('W','W')))
        for n in range(1,9):
            first=harness.fs(raw(base+('W',)),n)
            second=harness.fs(raw(base+('W','W')),n)
            assert first==raw(base+('A0',)*n)+(0,)
            child=('W','A0')*n
            assert second==raw(base+child)+(0,)
            assert std.is_standard(raw(base+child))
            finite_image=(0,0)+(0,)*n
            assert finite_image==harness.fs(YW,n)
            mapped=image_child(n);binary=harness.fs(YWW,n)
            assert binary==(0,0)+(1,0,0)*n
            assert binary[:-1]==mapped
            assert std.is_standard(mapped) and std.is_standard(binary)
            assert conj.o(mapped)==add(OMEGA*n,ONE)
            assert conj.o(binary)==add(OMEGA*n,nat(2))
            assert cmp(conj.o(harness.fs(YWW,n-1)),conj.o(mapped))<0
            assert cmp(conj.o(mapped),conj.o(binary))<0
            report['rows'].append(dict(base=base,n=n,token_child=child,token_raw_term=second,
                mapped=mapped,binary_term=binary,W_equal=True,WW_equal=False,
                extra_binary_terminal_contraction_equal=True))
        # These cofinal families force R_k to have order type omega*(k+1).
        for k in range(1,5):
            assert std.is_standard(raw(base+r(k)))
            assert std.is_standard(image_r(k)) and conj.o(image_r(k))==OMEGA*(k+1)
            for n in range(1,6):
                assert harness.fs(raw(base+r(k)),n)==raw(base+r(k-1)+('A0',)*(n+1))+(0,)
    cross_checks=0
    for n in range(1,9):
        for m in range(17):
            assert image_child(n)!=harness.fs(YWW,m)
            assert conj.o(image_child(n))!=conj.o(harness.fs(YWW,m))
            cross_checks+=1
    report['off_diagonal_checks']=cross_checks
    report['all_n_obstruction']='omega*n+1 != omega*m+2 for all n>=1,m>=1; m=0 gives2'
    report['cofinal_sandwich']='YWW[n-1] < image_child(n) < YWW[n]'
    (HERE/'reltail30-induced.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print('W',len(report['rows']),'exact matches; WW',len(report['rows']),'exact mismatches')
    print('off diagonal',cross_checks,'inequalities agree; extra binary terminal0 contraction matches all')


if __name__=='__main__':main()
