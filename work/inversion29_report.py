"""Render the measured cluster report as plain Japanese Markdown."""
import json
from pathlib import Path
from above_p_data26 import HERE
from inversion29 import tokens


def word(shape):
    ts=shape.get('tokens')
    text=' '.join(ts) if ts is not None else ''.join(map(str,shape['raw']))
    if shape.get('terminal'):text+=' ⌢ ('+','.join(map(str,shape['terminal']))+')'
    return text


def main():
    d=json.loads((HERE/'inversion29-clusters.json').read_text())
    out=['## 29. codex: seedの全順序違反を実際の項へ下降させた根の分類',
         '', '### 29.1 対象と下降の方法', '',
         '§28のWD_AFTER_ITERATION_EXPERIMENTによる値候補は棄却と明記しました。',
         '本節ではそのフラグをFalseに固定し、§27のseed候補だけを測定しています。値の規則は変更していません。', '',
         '対象は、N=9で標準なのにvalue-newを通らなかった1,892語です。',
         '生の列で重複を除くと1,139列。比較相手は§27の追加後の87,718標準列です。',
         '下側では値が最大、上側では値が最小の相手を選びました。両側が失敗する23列（24語）は両方を下降させました。',
         'そのため、開始する逆転の組は1,162組、別綴りの重みを含む経路数は1,916です。', '',
         '標準a<bかつV(a)≥V(b)から、b[n]≥aとなる最小nを実際のcutで求めます。',
         'V(b[n])<V(b)なら(a,b[n])を次の逆転とし、そうでなければそのbとnを根として記録しました。',
         '後継ではV(b)=V(bの末尾0を除いた列)+1を確認してから進みます。',
         'nに固定の上限は置かず、G⌢B^nの長さがaを越えるところまでを安全な探索範囲とした二分探索です。',
         '小さい範囲の19,110標準対で、線形探索の最小nと一致しました。', '',
         '### 29.2 全経路の結果', '',
         '全1,162経路が、実際の項の値が親未満でない根へ到達しました。',
         'Unknown、時間切れ、段数上限、no-gapsの失敗、後継・基底の別の根はすべて0です。',
         '計算は約123.9秒。全経路の38,078段を別の実行で再生し、最小n、逆転の維持、実際の項と値を確認しました。', '',
         '異なる親b*は77列、(b*,n)の組は87組です。77列の親と87組の子の標準性も直接確認しました。',
         '元のN=9の標準集合に入る根は36列、入らない根は41列でした。',
         '40列は正規化した部品表示でも10部品。残り1列はD D A4 A0 W D W W Dで、',
         '正規化表示は9部品ですが、元のアルファベットではA4をA3 Dと綴るため10部品です。',
         'したがって、範囲外の41列はすべて元の部品数の上限を越えます。',
         '今回の最大nは下降中も根でも3、最大段数は85でした。',
         '今回の見落としはn≤5の上限ではなく、下降で現れる長い列がN=9の集合外であることが主因です。', '',
         '根で使われたnの内訳は、n=1が648経路、n=2が299経路、n=3が215経路です。', '',
         '### 29.3 構文による10群', '',
         '先頭0021を省略します。最後の頭部A_kと、その後のW,Dの列で分類しました。',
         '第4群だけは末尾A2の直前の文脈も示しています。各群は重ならず、全経路を含みます。',
         '「組数」は生の列の開始対の数、「重み」は元の別綴りも数えた経路数です。', '',
         '| 群 | 末尾の形 | 異なる親 | (親,n) | 組数 | 重み | 根のn |',
         '| --- | --- | ---: | ---: | ---: | ---: | --- |']
    for c in d['clusters']:
        signature=' '.join([c['signature'][0]]+c['signature'][1])
        if c['id']==4:signature='A1 W D D A2'
        out.append(f'| {c["id"]} | {signature} | {c["parents"]} | {c["parent_n_roots"]} | {c["pairs"]} | {c["spelling_routes"]} | '+','.join(map(str,sorted(map(int,c['n_counts']))))+' |')
    out+=['', '最短の親と、実際に到達した子を次に示します。',
          '最短は正規化した部品数、次に部品タプルの辞書順で選びました。',
          'nは下降でaに届くための最小値です。単に値が親を越える最初の番号とは限りません。', '',
          '| 群 | 最短の`b*` | n | `b*[n]` |', '| --- | --- | ---: | --- |']
    for c in d['clusters']:
        r=c['representative']
        out.append(f'| {c["id"]} | {word(r["parent_shape"])} | {r["n"]} | {word(r["child_shape"])} |')
    out+=['', '### 29.4 親が小さいのか、項が大きいのか', '',
          '以下は、今の他の値を保持した場合の診断です。比較の相手も標準形であることを直接確認しました。',
          '値の規則自体が未証明なので、親か項のどちらを直せば真の順序数になるかの証明ではありません。',
          '特に、親を単独で大きくするだけでは、より上側の標準境界との逆転が残る群を項側の疑いとしました。', '']
    for c in d['clusters']:
        r=c['representative'];b=word(r['parent_shape']);e=c['comparisons'];j=c['judgement']
        out.append(f'第{c["id"]}群（{b}）:')
        out.append('')
        if j=='parent_too_small_relative_to_prefix':
            p=e['prefix'];w=word(tokens(tuple(p['raw'])))
            out += ['親が小さすぎる疑いです。末尾Dを付ける前の標準接頭辞Pを保持すると、',
                    f'`P = {w}` はb*より小さいのに、',
                    f'`V(P) = {p["value"]} > V(b*) = {r["parent"]}` です。',
                    'Dでそれまでの反復の文脈を落としていることを先に疑います。']
            if p.get('inference_equal') is False:
                out.append('ただしP自身にも5項のsup推定の不一致があるため、Pの値まで確定したという判断ではありません。')
        elif j=='parent_too_small_relative_to_lowered_A':
            p=e['lowered_A'];w=word(tokens(tuple(p['raw'])))
            out += ['親のA2側が小さすぎる疑いです。末尾をA1へ下げた標準接頭辞Lについて、',
                    f'`L = {w} < b*` なのに、',
                    f'`V(L) = {p["value"]} > V(b*) = {r["parent"]}` です。',
                    '第1項がL⌢(0,1)なので、新しくA2へ移る時点で既存の項の値を失うことが問題です。']
        elif j=='term_too_large_relative_to_D_bound':
            core=e['term_core'];u=e['larger_standard_bound']
            cw=word(tokens(tuple(core['raw'])));uw=word(tokens(tuple(u['raw'])))
            out += ['項側の深いAまたは複合コピーの作用が大きすぎる疑いです。',
                    f'子から末尾を除いた標準接頭辞 `C = {cw}` と、',
                    f'より大きい標準境界 `U = {uw}` を比べると、C<Uなのに、',
                    f'`V(C) = {core["value"]} > V(U) = {u["value"]}` です。',
                    '親b*だけを子に合わせて上げても、この上側境界との逆転は直りません。']
            if not e['larger_D']['standard']:
                out.append('単純に最後のWをDへ置き換えた語は非標準だったため、そのstd.ceilを境界Uとして使いました。')
            if 'first_A2' in e:
                f=e['first_A2'];fw=word(tokens(tuple(f['raw'])))
                out += [f'さらに最初のA2だけの標準語 `F = {fw}` でも、F<Uなのに',
                        f'`V(F) = {f["value"]} > V(U)` でした。',
                        'このF自身の5項のsup推定が親と一致しても、上側の別の標準形との順序は保証されません。']
        else:
            p=e['prefix'];core=e['term_core'];u=e['larger_standard_bound'];rank=e['copy_rank_comparison']
            out += ['項側の昇格を先に疑いますが、この群だけは判断が弱く、親側との二者択一を確定できません。',
                    '標準接頭辞P=b*の最後のWを除いた語と、子の接頭辞C、上側境界Uを比べると、',
                    f'`V(P) = {p["value"]}`、`V(b*) = {r["parent"]}`、',
                    f'`V(C) = {core["value"]}`、`V(U) = {u["value"]}` で、',
                    'V(P)<V(b*)<V(C)<V(U)です。上側D境界は越えていないので、他の群と同じ決め方は使えません。',
                    '追加の内部比較では、実際のコピーW D D Wに対し、',
                    f'保存する深さ0のrankは `{rank["stored_depth0"]}`、現在の深さ1の作用rankは `{rank["active_depth1"]}` です。',
                    '保存rankの方が大きく、この値を後のA2昇格へ持ち込む項側を優先して調べる、という判断です。',
                    'ここで保存rankを変更する修正はしていません。']
        out.append('')
    out += ['### 29.5 得られたことと再現', '',
            '全1,892語の失敗を、有限個の実際の親・項の矛盾へ落とせました。',
            '根が77列に集まることと、末尾の形が10群に分かれることは測定結果です。',
            'Dの文脈を落とす型、A2へ進んだ時点で値を落とす型、項がより大きい標準境界を越える型が分かれました。',
            'どの値を正しい値へ直すかは別の問題で、第10群の判断も含めて未確定の部分を残しています。',
            '新しい値の規則は追加していません。', '',
            '- [inversion29.py](work/inversion29.py)：全失敗対の下降と最小nの計算。',
            '- [inversion29_clusters.py](work/inversion29_clusters.py)、[inversion29-clusters.json](work/inversion29-clusters.json)：10群の件数、代表、追加比較と診断。',
            '- work/inversion29.json.gz：全1,162経路、38,078段、到達した親と項の値・標準性。', '',
            '```bash', 'timeout 600 python3 work/inversion29.py',
            'timeout 180 python3 work/inversion29_clusters.py', '```', '',
            '全経路の再生、全87組の根の標準性・値の逆転、群の件数と別綴りの重みを独立に確認しました。',
            '先方のinversion_descent.pyによる指定の2例とも、同じ根・番号を確認しました。',
            'README、Leanファイル、値の規則、各フラグの既定値は変更していません。', '']
    (HERE/'inversion29-report.md').write_text('\n'.join(out))


if __name__=='__main__':main()
