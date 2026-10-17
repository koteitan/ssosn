"""Test partial patterns against fresh NOREGION values; never use old valuations."""
import argparse
import json
from pathlib import Path
import pickle
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]
import conj
import lift
import rule6
from ordinal import ONE, ZERO, OMEGA, P, add, nat, w
from order_region import tu


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--state', type=Path, required=True)
    ap.add_argument('--evaluation', type=Path, required=True)
    ap.add_argument('--output', type=Path, default=HERE/'noregion-patterns.json')
    ap.add_argument('--w-output', type=Path, default=HERE/'noregion-W-proposal.json')
    args = ap.parse_args()
    with args.state.open('rb') as f:
        state = pickle.load(f)
    assert state['signature'][0] == 'noregion-no-II-v1'
    rows = json.loads(args.evaluation.read_text())['rows']
    rule6.NOREGION = rule6.EXT = True
    rule6.EXT121 = rule6.EXT121E = False
    rule6.memo, rule6.hmemo = state['memo'], state['hmemo']
    base = (0, 0, 2, 1, 0, 1, 2, 1)
    a1 = (0, 1, 2, 0, 2)
    agreements, differences, uncovered, wc = [], [], [], []
    eomega = P(ONE, OMEGA)
    for row in rows:
        if row['ordinal'] is None:
            continue
        s = tuple(map(int, row['sequence']))
        actual = tu(row['ordinal'])
        assert state['memo'][s] == actual
        found = False
        # Use the maximal initial run of A1, rather than re-reading its tail
        # as a different binary lift suffix.
        for k in range(9, 0, -1):
            prefix = base+a1*k
            if s[:len(prefix)] != prefix:
                continue
            y = lift.unlift((2, 1)+s[len(prefix):])
            if y is None:
                continue
            prediction = P(ONE, add(add(eomega, w(nat(k+2))), conj.v(y)))
            item = dict(sequence=row['sequence'], k=k, binary=y,
                        prediction=prediction, actual=actual)
            (agreements if prediction == actual else differences).append(item)
            found = True
            break
        if not found:
            uncovered.append(row['sequence'])
        u = s[2:]
        if u[-4:] != (0, 1, 2, 1) or u[-7:] == (0, 1, 2, 0, 1, 2, 1):
            continue
        up = u[:-4]
        value = state['hmemo'].get(up)
        if value is None or len(value) != 1 or value[0][1] != ONE:
            continue
        index = value[0][2]
        depth = rule6.lev(up)
        if not 1 <= depth < rule6.INF:
            continue
        # A proposal fitted after the independent evaluation, not an evaluator.
        step = ONE if len(index) > 2 and index[-1][1] == ZERO and index[-1][2] else OMEGA
        bumped = rule6.bump(index, depth, step, rule6.ext_base(up))
        if bumped is None:
            continue
        prediction = P(ONE, bumped)
        wc.append(dict(sequence=row['sequence'], up_index=index, depth=depth,
                       a=step, prediction=prediction, actual=actual,
                       agree=prediction == actual))
    report = dict(rule='Q_k emit(Y) -> epsilon_(epsilon_omega + omega^(k+2) + v(Y)); conjectural',
                  corpus_resolved=len(agreements)+len(differences)+len(uncovered),
                  agree=agreements, differ=differences, uncovered=uncovered)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    args.w_output.write_text(json.dumps(dict(
        method='fresh index as input; additive omega tail uses +1, bare power uses +omega; proposal only',
        cases=wc), ensure_ascii=False, indent=2)+'\n')
    print('partial lift pattern', len(agreements), len(differences), len(uncovered))
    print('W proposal', sum(x['agree'] for x in wc), 'of', len(wc))


if __name__ == '__main__':
    main()
