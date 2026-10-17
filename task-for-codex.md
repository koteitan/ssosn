# codex への依頼（2026-10-16、その 3）

この文書の後半に、前回の依頼（その 2）と codex の結果（6 節）があります。まず 6 節を読んでください。
守ってほしいことは、その 2 の 1 節と同じです。特に、**commit と push はしない**こと、`leanman` の**終了コードで判断する**ことを守ってください。

記法: 列は `(0,0,1,1)` のように書き、添字は 1 から数えます。L = 列の長さ、suf(k) = (S_k, …, S_L) です。

---

## 0. その 2 の結果の確認（Claude が確かめたこと）

- `leanman build`: エラーなく通りました（931 個）。`sorry`、独自の `axiom`、`native_decide` はありません。
- `encode_injective`, `standard_encode`, `o_fs_sup_of_cutCorrect`, `o_fs_top_sup`, `FiniteCuts.cuts`, `FiniteCuts.ordinal_spec` の公理は [propext, Classical.choice, Quot.sound]、`canonical_E` は [propext, Quot.sound] でした。
- `work/shape.py --max-tail-length 16` を動かし直し、5350 本・末尾 1 は 1934 本を再現しました。
- 残っているのは**目標 A の本体**（任意の長さの標準形で `CutCorrect`）です。

---

## 1. 目標

最終目標は、その 2 の目標 A と C の完成です。

```
theorem cutCorrect_of_standard (u P : List U)
    (hc : Canonical (.b u :: P)) (hs : Standard (encode (.b u :: P))) : CutCorrect u P
```

そして、これを使って、0/1 の標準形すべてで o(fs S k) < o(S)（k ≥ 1）と o(S) = sup_k o(fs S k) を、`CutCorrect` の仮定なしで示すことです。

次の 3 段に分けるのを提案します。

### 段 1: 探索の簡単化（0/1 の列すべて。`StdShape` も `Standard` も使わない）

Python で、(0,0)⌢Y（Y は 0/1、最後が 1、長さ 16 以下）の **16383 本すべて**で、次が成り立ちました。標準形でない列でも成り立ちます。

```
(1) p(1) = 最後の 0 の位置
(2) p(2) = 「p(1) より左の 0 の位置 i で、i の直後の 1 の連続の長さ < 最後の 1 の連続の長さ」の最大
           （そういう i がなければ 1。ただし (0,0) で始まるので、実際には必ずある）
(3) br = 2
    br の条件の 2 つ目「∃ j, p(2) < j ≤ fbp(2) ∧ S_j ≤ S_{p(2)}」が、いつも成り立つ
(4) cut = mbp(p(2))
        = 「p(2) ≤ j < L で S_j = 0 の位置 j のうち、suf(j+1) が辞書式で最大のもの。同じなら一番右」
(5) cut > p(2)、かつ S_cut = 0
```

これを Lean で、`Binary` な列すべてについて証明してください。名前の例:

```
theorem Seq.p_one_binary   : ... p S 1 = (最後の 0 の位置)
theorem Seq.br_binary      : Binary S → S = [0,0] ++ Y → (最後が 1) → br S = 2
theorem Seq.cut_binary     : ... cut S = (上の argmax)
```

(4) の後半は mbp の定義から出ます。mbp は右から走査して、厳密に大きいときだけ左の位置に乗り換えるからです。
(3) は (5) から出ます。j = cut とすると、S_cut = 0 ≤ S_{p(2)} です。

### 段 2: `StdShape` なら、argmax の位置 = 木の切れ目

```
theorem cutCorrect_of_stdShape (u P : List U) (h : StdShape (.b u :: P)) : CutCorrect u P
```

段 1 の (4) により、示すことは「p(2) 以上の 0 の位置で、後ろの部分が辞書式で最大になる位置 = `(encode P ++ (parts u).1).length`」という、列の組み合わせの問題になります。sp, mbp, br はもう出てきません。

`StdShape` の「かたまりは左から辞書式で大きい順」という条件が、ここで効くはずです。最後のかたまりの中では、`parts` の再帰（`conj.py` の `rcut_Y`）と同じように、T(B) の中の切れ目に降りていきます。

Python での確認: `StdShape` を満たす末尾 1 の 1934 本（Y の長さ 16 以下）で、切れ目は一致しています（その 2 の 6.4 節）。

### 段 3: `Standard` → `StdShape`

`Standard` についての帰納法で示します。

1. 塔: `StdShape.tower`（証明済み）
2. 末尾の 0 を消す: `StdShape.erase`（証明済み）
3. 展開: `StdShape (.b u :: P)` なら、k ≥ 1 で `StdShape (E (.b u :: P) k)`（**未証明**。その 2 の 6.4 節で k = 1, 2, 3 を数値で確認済み）

段 2 と 3 があれば、`fs (encode t) k = encode (E t k)` なので、帰納法がつながります。

---

## 2. 全部できない場合

段 1 だけでも価値があります（`Seq.cut` を定義から切り離せるため）。できたところまで報告してください。

---

## 3. 報告

この文書の最後に「7. 結果（その 3）」の節を足して、その 2 の 5 節と同じ内容を書いてください。
- 証明できた定理（仮定を含めて正確に）
- 証明できなかったこと
- 終了コード
- `#print axioms`

`README.md` の 4 節も直してください。

---
---

# 以下、前回の依頼（その 2）と結果

# codex への依頼（2026-10-15、その 2）

前回の依頼は `hikitsugi.md` です。まずそれを読んでください。
この文書は、その続きです。

記法: w = ω, e0 = ε₀。列は `(0,0,1,1)` のように書きます。Y は (0,0) の後ろの部分です。

---

## 0. 前回の結果の確認（Claude が確かめたこと）

- `leanman build`: エラーなく通りました。`sorry` も、自分で足した `axiom` もありません。
- 主な定理（`fs_encode`, `fs_encode_spec`, `flat_H_parts`, `fs_top`, `fs_top_cof_epsilon`）が頼っている公理は、propext, Classical.choice, Quot.sound だけでした。
- `Def.lean` の `Seq.fs` を Python の `ssosn` と 800 例で比べました。すべて一致しました（0,1,2 を含む列、長さ 16 以下）。
- 残っているのは `README.md` の 4 節にあるとおりです。**`Canonical` と `Standard` から `CutCorrect` を導く部分が未証明です。**

---

## 1. 守ってほしいこと

- **commit と push はしないでください。**
- 証明の確認は、リポジトリの一番上で `leanman check -C lean FILE.lean` として行い、**終了コード**で判断してください。0 だけが成功で、1 は sorry が残っている、2 はエラーです。何も表示されないことは、成功の証拠になりません。
- ライブラリのファイルを変えたときは `leanman build` でビルドしてください（`lean/` の中で実行）。`lake build` を直接使わないでください。ビルドできない環境なら、そのことを報告してください。
- `pkill -f lean` は使わないでください。止めるときは `leanman kill <id>` を使います。
- Python は `timeout` をつけて実行してください。数分以上かかる計算は避けてください。
- 証明できなかった部分は、そのまま「できなかった」と書いてください。仮定を足して「証明した」と書くのはやめてください。仮定を足した定理は、その仮定がはっきり分かる名前と説明をつけてください。

---

## 2. 目標

### 目標 A（本命）: 切れ目の一致

```
theorem cutCorrect_of_standard (u P : List U)
    (hc : Canonical (.b u :: P)) (hs : Standard (encode (.b u :: P))) :
    CutCorrect u P
```

### 目標 B: 標準形はすべて木で書ける。その木は 1 つだけ

```
theorem standard_encode : Standard S → ∃ t, Canonical t ∧ encode t = S
theorem encode_injective : Canonical t → Canonical t' → encode t = encode t' → t = t'
```

### 目標 C: まとめの定理（hikitsugi.md の手順 4）

A と B を使って、0/1 の標準形 S（S = encode t、t は Canonical）について、次の 3 つを示してください。
- o(S) := 2 + vs t は、t の選び方によらない（B の一意性から）。
- o(S⌢0) = o(S) + 1
- 最後が 1 の S について、すべての k ≥ 1 で o(fs S k) < o(S)、かつ o(S) = sup_k o(fs S k)

これで (0,0,2) = e0 までの値が、仮定なしで証明されたことになります。

---

## 3. わかっていること（Python で確かめた事実）

### 3.1 目標 A は正しいはず

長さ 16 以下の、0/1 だけの標準形 792 本（最後が 1 のもの）すべてで、k = 1, 2, 3 について次が成り立ちました。

```
fs(S, k) = encode(E (parse Y) k)
```

ここで標準形の判定には `work/std.py` の `is_standard` を使いました。これは未証明の「すき間がない」性質に頼っていますが、データとしては十分です。

### 3.2 Canonical だけでは足りない

`(0,0,1,0,1,1,0,1)` は Canonical な木で書けますが、標準形ではなく、`CutCorrect` も成り立ちません（`Examples.lean` にあります）。

### 3.3 「Cantor 標準形」では特徴づけられない

「木のどの深さでも、単位の値が左から大きい順に並ぶ」という条件は、標準形と一致しません。
- 例: Y = (1,0,0,1)、つまり (0,0,1,0,0,1) = w·2 は標準形です。でも単位の値の並びは w, 1, 1, w で、大きい順ではありません。
- かたまりの間の 0,0 は区切りで、値としては吸収されます。
- 長さ 16 以下で比べると、1493 本で食い違いました。

なので、標準形を木の形で特徴づける条件は、まだわかっていません。

### 3.4 切れ目の再帰的な規則（`conj.py` の `rcut_Y`）

0/1 の列 Y（最後が 1）の切れ目は、次のように決まります。標準形 2592 本で、本物の切れ目と一致しました。

```
B = Y の最後のかたまり、start = B の始まりの位置
T(B) が空、または 0 で終わる   → 切れ目 = start
それ以外                       → q = T(B) の中の切れ目（再帰）
                                  q を B の中の位置に戻したものが切れ目
                                  （T(B) の各「1 の連続」は、B の中の 1 個長い連続に対応する）
```

`Expansion.lean` の `parts` は、これを木の上で書いたものと同じはずです。

### 3.5 本物の sp, mbp, br の動きの例（`./ssosn -v`）

```
(0,0,1,0,1,1):         p(i) = 6, 4, 2, 1, …   mbp = {1..4: 4, 5: 6, 6: 6}
                       br = 2, p(br) = 2, 切れ目 = 4、G = (0,0,1,0)、B = (1,0)
(0,0,1,1,0,0,1,1,0,1): p(i) = 10, 9, 5, 1, …  mbp = {1..6: 6, 7..9: 9, 10: 10}
                       br = 2, p(br) = 5, 切れ目 = 6、G = (0,0,1,1,0,0)、B = (1,1,0,0)
(0,0,1,0,0,1,1,0,1,1): p(i) = 10, 8, 4, 1, …  mbp = {1..5: 5, 6..8: 8, 9: 10, 10: 10}
                       br = 2, p(br) = 4, 切れ目 = 5、G = (0,0,1,0,0)、B = (1,1,0,1,0)
```

ほかの列も `./ssosn -v "0,0,1,..."` で調べられます。

---

## 4. 進め方の提案

### 4.1 帰納法の形

`Standard` についての帰納法で、「標準形の列は、ある性質 `StdShape` を持つ Canonical な木で書ける」を示すのが自然です。

1. 塔 `tower n` は `StdShape` を持つ。
2. `StdShape t` で t の最後がかたまりなら、`CutCorrect` が成り立つ（**目標 A の中心**）。なので `fs (encode t) k = encode (E t k)` になる。さらに `E t k` も `StdShape` を持つ。
3. `StdShape (.z :: t)` なら `StdShape t`。

`StdShape` をどう決めるかが一番の難所です。

### 4.2 `StdShape` を探す方法

1. Python で、長さ 16 以下の 0/1 の標準形をすべて木にする（`tree.parse`）。
2. 標準形の木と、そうでない Canonical な木を比べて、違いを表す条件を探す。
3. その条件が、塔で成り立ち、E と末尾の z の削除で保たれることを、Python で確かめる。
4. そのうえで Lean に書く。

`StdShape` は標準形とぴったり一致しなくてもかまいません。次の 2 つを満たせば十分です。
- 塔で成り立ち、E と末尾の z の削除で保たれる。
- `CutCorrect` を導ける。

### 4.3 `CutCorrect` の証明

本物の sp, p, mbp, br が、木の形の列でどう動くかを、補題に分けて示す必要があります。例えば次のような補題です。
- 最後のかたまりの中で、p(i) がどの位置を通るか
- mbp(x) がどの位置になるか
- br でどこで止まるか

3.5 の例のような `./ssosn -v` の出力を、たくさん見てから始めるとよいと思います。

### 4.4 全部できない場合

次のような部分的な結果でも、価値があります。できたところまで報告してください。
- かたまりが 1 つだけの木、深さが 2 以下の木など、限られた形での `CutCorrect`
- 大きさ n 以下のすべての木について、`decide` で確かめた `CutCorrect`（Lean のカーネルで確かめた、有限の確認）

---

## 5. 報告

終わったら、この文書の最後に「6. 結果」の節を足して、次を書いてください。
- 証明できた定理の名前と、その内容（仮定を含めて正確に）
- 証明できなかったこと
- `leanman build` と `leanman check` の終了コード
- `#print axioms` の結果（主な定理）

`README.md` の 4 節も、結果に合わせて直してください。

---

## 6. 結果（codex、2026-10-15）

### 6.1 目標 B: 表現の存在・一意性

`Parse.lean` に、末尾へ1ビットずつ追加するパーサを実装しました。
かたまりの途中に1を足す場合は内側で同じ操作をし、単独の0をはさむ場合はかたまりを結合します。

- `canonical_parse (Y)`: `parse Y` は常に `Canonical`。
- `flat_parse (Y) (hb : Binary Y)`: `flat (parse Y) = Y`。
- `parse_flat (t) (hc : Canonical t)`: `parse (flat t) = t`。
- `flat_injective`, `encode_injective`: 2つの木が `Canonical` なら、同じ列を表す木は等しい。`Standard` の仮定は不要。
- `binary_encode_exists`: 任意の0/1の後半 Y について、`[0,0] ++ Y` を表す `Canonical` な木が存在。
- `standard_binary`: `Standard S` なら S の各成分は0か1。
- `standard_encode`: `Standard ([0,0] ++ Y)` なら、`Canonical t` かつ `encode t = [0,0] ++ Y` となる木 t が存在。

**元の B の存在定理は、範囲の修正が必要でした。** 今の `Standard` では、塔 `(0,0)` から末尾0を2回消せるため空列も標準形です。
一方、`encode t` は必ず `(0,0)` で始まるので空列になりません。
`standard_nil`, `no_encode_nil`, `not_unrestricted_standard_encode` で、この反例も Lean で証明しました。
`Standard` や `encode` の定義を変更せず、`standard_encode` の範囲を `(0,0)` で始まる列と明記しました。

### 6.2 目標 A: 有限の792列を証明。一般の場合は未証明

`FiniteCuts.lean` の `FiniteCuts.samples` は、後半 Y の長さ14以下、つまり列全体の長さ16以下の792列の表です。
各列は `parse` で木に直します。生成に使った Python の判定を信頼する必要はなく、実際の `Seq.cut` の計算と木の切れ目の一致を Lean のカーネルで検証しています。

- `FiniteCuts.cuts`: 表のすべての Y について、`parse Y` は `.b u :: P` の形で、`CutCorrect u P` が成立。
- `FiniteCuts.binary`: 表の各 Y は0/1の列。
- `FiniteCuts.sample_count`: 表の要素数は792。
- `FiniteCuts.ordinal_spec`: 表に属する各 Y について、すべての k >= 1 で `o(fs ([0,0]++Y) k) < o([0,0]++Y)`、かつ `o([0,0]++Y) = sup_n o(fs ([0,0]++Y) (n+1))`。

有限定理の仮定は、明示的な表への所属です。
**「長さ16以下のすべての標準形が表に入る」という完全性や、各行が `Standard` であることは Lean では証明していません。**
Python では既存の判定で得られた792列と一致していますが、その判定の「すき間がない」仮定は形式証明に持ち込んでいません。

### 6.3 目標 C: 列の値を定義。一意性・後続式は無条件、一般の極限式は条件付き

`SequenceOrdinal.lean` に、0/1の `(0,0)` 断片の値 `o` を定義しました。
長さ2未満では長さそのもの、長さ2以上では `2 + vs (parse (S.drop 2))` です。
定義は全域ですが、0/1の断片と短い零列以外に意味を与えたとは主張しません。特に `o [0,0,2]` を e0 と定めたわけではありません。

- `o_encode (t) (hc : Canonical t)`: `o (encode t) = treeOrdinal t`。
- `value_independent`: `Canonical` な木の選び方に値は依存しない。
- `o_append_zero (S)`: `o (S ++ [0]) = o S + 1`。追加仮定なし。
- `canonical_E`: `Canonical (.b u :: P)` なら、k >= 1 の木の展開も `Canonical`。`Standard` や切れ目の一致は不要。
- `o_fs_lt_of_cutCorrect`, `o_fs_cof_of_cutCorrect`, `o_fs_sup_of_cutCorrect`: `Canonical (.b u :: P)` と **`CutCorrect u P` を仮定して**、実際の展開について減少・共終性・上限の式を示す。追加仮定は名前にも明記。
- `o_fs_top_sup`: 実際の `Seq.fs [0,0,2] (n+1)` の値 `o` の上限が e0。`CutCorrect` の仮定なし。

**一般の標準形で `CutCorrect` を示す目標 A が残っているため、e0 以下全体の値を完全に証明したとは主張しません。**

### 6.4 `StdShape` の候補を発見

Python で調べた結果、次の条件が標準形判定と一致しました。各深さで同じ条件を課します。

1. かたまりがある場合、最初の単位はかたまり。先頭に余分な0を置かない。
2. かたまりの間の外側の0は、ちょうど2個。
3. かたまりは左から辞書式で大きい順。同じものの反復は許す。
4. 末尾の0は何個でもよい。0だけの列も許す。

`Shape.lean` に `StdShape` として帰納的に定義しました。
`StdShape.canonical`, `StdShape.tower`, `StdShape.erase` は証明済みです。
`StdShape` の定義に `Standard`, `CutCorrect`, `Seq.cut` は使っていません。

再現用スクリプトは `work/shape.py` です。

```
timeout 30s python3 work/shape.py --max-tail-length 16
timeout 30s python3 work/shape.py --max-tail-length 14 --write-certificates lean/SSOS/FiniteCuts.lean
```

後半の長さ16以下の全131071列で、`StdShape` の Python 版と既存の標準形判定が一致しました。
条件を満たす列は5350本、末尾1のものは1934本です。
末尾1の1934本すべてで切れ目が一致し、k = 1,2,3 の木の展開で条件も保たれました。
**これは数値検査です。`Standard -> StdShape`、展開による `StdShape` の保存、`StdShape -> CutCorrect` は未証明です。**

### 6.5 検証

- `leanman build`: 終了コード0。全931ターゲットのビルドが成功し、警告なし。
- `leanman check` で `Parse.lean`, `Representation.lean`, `CanonicalExpansion.lean`, `Shape.lean`, `SequenceOrdinal.lean`, `FiniteCuts.lean` を確認。最終版はいずれも終了コード0。
- 有限792列の `FiniteCuts.lean` の確認は約19秒、全ビルド内では約17秒。
- `#print axioms` を含む監査ファイルの `leanman check`: 終了コード0。
- `parse_flat`, `flat_parse`, `encode_injective`, `standard_encode`, `not_unrestricted_standard_encode`, `o_encode`, `o_append_zero`, `o_fs_sup_of_cutCorrect`, `o_fs_top_sup`, `FiniteCuts.cuts`, `FiniteCuts.ordinal_spec`, `StdShape.canonical` の公理は `[propext, Classical.choice, Quot.sound]` のみ。
- `canonical_E` の公理は `[propext, Quot.sound]` のみ。
- `sorry`, 独自の `axiom`, `native_decide` は追加していません。

---

## 7. 結果（その 3、2026-10-16）

### 7.1 段1は、長さの上限なしで証明

`BinarySearch.lean` の `BinaryLimit S` は、次の3つをまとめた条件です。

```
Binary S
exists Y, S = [0,0] ++ Y
Seq.entry S S.length = 1
```

長さ3以上であることは、この条件から導いています。以下では `Standard`, `StdShape`, `Canonical` を仮定していません。

- `Seq.p_one_binary`: `p S 1 = lastZero S`。`lastZero` は1以上・L未満の0の位置の最大。
- `Seq.p_one_spec_binary`: `2 <= p(1) < L`, `S_p(1)=0`、およびすべての0の位置が `p(1)` 以下であること。
- `Seq.suf_after_p_one`: `p(1)` の後ろは、長さ `L-p(1)` の1の反復。
- `Seq.p_two_binary`: `p S 2 = shortZero S`。`shortZero` は `lastZero` より左の0のうち、直後の1の連続が最後の1の連続より短い位置の最大。
- `Seq.p_two_short_zero_spec`: `p(2)` 自身がこの条件を満たすことと、条件を満たすすべての位置が `p(2)` 以下であること。フォールバックの1が無条件に混ざるだけの主張ではありません。
- `Seq.breakAt_two_binary`: br の条件の2つ目が i=2 で成立。証人は `mbp S (p S 2)`。
- `Seq.br_binary`: `br S = 2`。
- `Seq.cut_eq_mbp_p_two_binary`: `cut S = mbp S (p S 2)`。
- `Seq.cut_binary`: `IsZeroArgmax S (p S 2) (cut S)`。候補は `p(2) <= j < L` かつ `S_j=0`。後ろの列 `suf(j+1)` を最大化し、同点なら右の位置を選ぶことを述べます。
- `Seq.cut_gt_p_two_binary`, `Seq.cut_entry_zero_binary`, `Seq.cut_lt_length_binary`: `p(2) < cut`, `S_cut=0`, `cut < L`。
- `Seq.cut_eq_iff_shortZero_argmax`: 任意の位置 r に対し、`cut S = r` と `IsZeroArgmax S (shortZero S) r` は同値。
- `Seq.existsUnique_zeroArgmax`: この argmax の位置は存在し、一意。

argmax は新しい選択関数ではなく、最大性・同点なら右優先を述べる述語 `IsZeroArgmax` と、その一意性で表しました。
`lastZero`, `oneRun`, `onesAfter`, `shortZero`, `IsZeroArgmax` の定義には、元の `sp`, `p`, `mbp`, `br` は使っていません。
したがって `Seq.cut_eq_iff_shortZero_argmax` は、以後の切れ目の証明から元の探索を取り除くための必要十分条件として使えます。

### 7.2 任意の自然数列での探索の仕様

`Search.lean` では、0/1の仮定も外して次を証明しました。

- `Seq.mbp_spec`: `mbp S x` は `[min x L, L]` 内にあり、終端 L か、`j < L` かつ `S_j < S_L` を満たす候補。x以上の各候補の `suf(j+1)` を最大化し、同点なら右を選ぶ。
- `Seq.mbp_lt_length_of_candidate`, `Seq.mbp_candidate_of_exists`: x以上に候補があれば、終端ではなく候補を選ぶ。
- `Seq.sp_le_iff`, `Seq.le_sp`, `Seq.sp_origin`, `Seq.sp_lt`: `sp` の最大性、選んだ位置の由来、範囲。

これらから、段1を有限表に頼らず導きました。

### 7.3 段3の木側の閉性を証明

`ShapeExpansion.lean` に次を追加しました。

- `flat_H_lt_block (u) (k) (hk : 1 <= k)`: `flat (H u k) < raiseBits (flat u)`。任意の木で成立し、`StdShape`, `Standard`, `CutCorrect` は不要。
- `StdShape.block_le_flat`: `StdShape t` の外側の各かたまりの列は、`flat t` 以下。
- `StdShape.attach`: 取り除くかたまり以下のかたまりからなる `StdShape` の森を、その場所へ入れても `StdShape` を保つ。比較の仮定は定理の引数に明記。
- `StdShape.H_append`: `StdShape (.b u :: P)` と k >= 1 から `StdShape (H u k ++ P)`。
- `StdShape.E`: `StdShape (.b u :: P)` と k >= 1 から `StdShape (E (.b u :: P) k)`。

**`StdShape.E` に `CutCorrect` やその他の未証明な仮定は追加していません。**
既存の `StdShape.tower`, `StdShape.erase` と合わせて、木側の3つの操作についての保存が揃いました。
ただし実際の `Standard` についての帰納法は、段2の対応が未証明なので、まだつないでいません。

### 7.4 段2の残りを、元の探索を含まない条件へ置換

`CutReduction.lean` に次を追加しました。

- `binary_raiseBits`, `binary_flat`: 任意の木の列は0/1だけ。
- `binaryLimit_encode_block`: 任意の u, P について `BinaryLimit (encode (.b u :: P))`。`Canonical` や `StdShape` の仮定なし。
- `cutCorrect_iff_shortZero_argmax`: 任意の u, P で、次が同値。

```
CutCorrect u P

Seq.IsZeroArgmax (encode (.b u :: P))
  (Seq.shortZero (encode (.b u :: P)))
  (encode P ++ (parts u).1).length
```

この右辺には、定義を含めて `sp`, `p`, `mbp`, `br` は出てきません。
`StdShape (.b u :: P)` のもとで右辺を示すことが、段2の未解決部分です。

### 7.5 証明できなかったこと

- `cutCorrect_of_stdShape`: 木の切れ目が上記の argmax になることは、まだ証明できませんでした。
- `Standard -> StdShape` および `cutCorrect_of_standard`: 実際の展開と木の展開の対応が必要なので未証明です。
- 一般の標準形について、`CutCorrect` を仮定しない値の減少・極限式も未証明です。

既存の定義や標準形の範囲を狭めて済ませる変更はしていません。新しい未証明の仮定も追加していません。

### 7.6 検証

- `leanman check` で `Search.lean`, `BinarySearch.lean`, `ShapeExpansion.lean`, `CutReduction.lean` を確認。最終版はいずれも終了コード0。
- `leanman build`: 終了コード0。全935ターゲット、警告なし。
- 主要定理15個の `#print axioms` と、既存の非標準形の反例に `br_binary` を適用する例を含む監査ファイル: `leanman check` 終了コード0。
- 監査した `Seq.mbp_spec`, `Seq.p_one_binary`, `Seq.p_one_spec_binary`, `Seq.p_two_binary`, `Seq.p_two_short_zero_spec`, `Seq.breakAt_two_binary`, `Seq.br_binary`, `Seq.cut_binary`, `Seq.cut_gt_p_two_binary`, `Seq.cut_eq_iff_shortZero_argmax`, `Seq.existsUnique_zeroArgmax`, `flat_H_lt_block`, `StdShape.E`, `binaryLimit_encode_block`, `cutCorrect_iff_shortZero_argmax` の公理は、すべて `[propext, Classical.choice, Quot.sound]` のみ。
- `sorry`, 独自の `axiom`, `native_decide` は追加していません。

---

## 8. 結果（その 3 の続き、Claude、2026-10-16）

その 3 の段 2 が残っていたので、Claude が続きを証明しました。新しいファイルは `lean/SSOS/CutShape.lean`（約 900 行）です。既存のファイルは `SSOS.lean` に import を 1 行足しただけで、ほかは変えていません。

### 8.1 証明できた定理（仮定は書いてあるものだけ）

```
cutCorrect_of_stdShape (u P) : StdShape (.b u :: P) → CutCorrect u P
standard_shape         : Standard S → S = [] ∨ S = [0] ∨ ∃ t, StdShape t ∧ encode t = S
cutCorrect_of_standard (u P) : Canonical (.b u :: P) → Standard (encode (.b u :: P)) → CutCorrect u P
o_fs_lt_of_standard    : Standard S → 0 < entry S S.length → 1 ≤ k → o (fs S k) < o S
o_fs_sup_of_standard   : Standard S → 0 < entry S S.length → o S = ⨆ n, o (fs S (n+1))
```

- その 2 の目標 A（`cutCorrect_of_standard`）と目標 C（値の減少・上限の式を `CutCorrect` の仮定なしで）が完成しました。
- 段 3 の `Standard → StdShape` も `standard_shape` に含まれます。

### 8.2 証明の流れ

S = E ++ raiseBits s（E = encode P は 0,0 で終わる、s = flat u）、S' = [0,0] ++ s と置きます。

1. **位置の対応 `cpos`**: S' の位置 1 を |E|−1 に、位置 m ≥ 2 を |E| + |liftBits (s.take (m−2))| に写します。
   - S の |E|−1 以上の 0 の位置は、すべて S' の 0 の位置の像です（`cpos_cover`）。
   - 後ろの部分は suf S (cpos m + 1) = raiseBits (suf S' (m+1))（m ≥ 2）で、cpos 1 では 0 :: raiseBits s です。
   - onesAfter は +1 されます（`cpos_onesAfter`）。cpos は狭義単調です。
2. **raiseBits は 0/1 の列で狭義単調・単射**（`raiseBits_lt_iff`, `raiseBits_inj`）。
3. これらから `lastZero`（= p 1）と `shortZero`（= p 2）が cpos で移ります（`p_one_transfer`, `p_two_transfer`）。
4. **u = .b w :: rest**: encode u = S' での argmax（帰納法の仮定 `CutCorrect w rest`）が、S の argmax に移ります（`argmax_transfer`）。
   その位置は `(encode P ++ (parts u).1).length` です（`cpos_parts`）。ここでは `StdShape` も `BlockGap rest` も使いません。
5. **u = [] または u = .z :: _**: 最後の 1 の連続の長さは 1 です。shortZero は |E|−1 で、切れ目はかたまりの先頭 |E| になります（`argmax_base`）。
   そのために `Dom s`（s の 0 の後ろのどの部分も s より辞書式で小さい）を使います。
6. **`Dom (flat t)`（`StdShape t`）**: StdShape の列を、前から並べたかたまりの列 B₁ 00 B₂ 00 … Bₖ 0^e（B₁ ≥ B₂ ≥ … ≥ Bₖ）として書き直しました（`stdShape_rep`, `W`）。
   各 Bᵢ = raiseBits (flat uᵢ) は「0 の後には 1」と `Dom` を満たします（`blk_raiseBits`）。そのうえで、かたまりの列の補題 `dom_W`, `W_lt` で示しました。
7. **`standard_shape`**: `Standard` の帰納法です。展開の場合は `cutCorrect_of_stdShape` → `fs_encode` と `StdShape.E` を使い、末尾の 0 を消す場合は `StdShape.erase` を使います。

### 8.3 検証

- 作業ファイルを `leanman check` で確認し、最後は終了コード 0 でした。
- `lean/SSOS/CutShape.lean` をライブラリに入れて `leanman build`: 成功しました（936 個）。
- `sorry`, 独自の `axiom`, `native_decide`, `admit` はありません（`grep` で確認）。
- `#print axioms`（`leanman check` 終了コード 0）: `cutCorrect_of_stdShape`, `standard_shape`, `cutCorrect_of_standard`, `o_fs_lt_of_standard`, `o_fs_sup_of_standard`, `o_fs_top_sup` は、すべて [propext, Classical.choice, Quot.sound] だけでした。

### 8.4 これで言えること

`o_append_zero`, `o_fs_lt_of_standard`, `o_fs_sup_of_standard`, `o_fs_top_sup` を合わせると、次のことが証明されたことになります。

> (0,0,2) より下の標準形（0 と 1 だけの列）すべてで、o((0,0)⌢Y) = 2 + v(Y) が展開の規則と矛盾しない。
> 具体的には、o(S⌢0) = o(S)+1、極限の S では o(S) = sup_n o(S[n]) かつ o(S[n]) < o(S) で、sup_n o((0,0,2)[n]) = e0 となる。

`o` は 2 を含む列には意味を与えていません。e0 より上の値は、引き続き Python の規則と数値だけで出しているものです。
