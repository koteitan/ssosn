import SSOS.VCut

/-!
# Cut laws for the tokens after `P = (0,0,2,1,0,2)` (§43 of the 2026-10-17 notes)

Tokens: `A_k = (0,1,2)⌢(0,2)^k`, `W = (0,1,2,1)`, `D = (0,2)`, `V = (0,2,1)`, `Z = (0)`,
`L_k = (0,1^k)`.

The general laws state the parent and record searches as suffix comparisons
(`GeAll`, `TailsLe`), so they hold after every prefix `Y`:

* `cut_unit_br2`, `fs_unit_br2`: a last unit `0⌢M'⌢h` (`h > 0`, every suffix of `M'⌢h` at
  least `(h)`), the second parent `c` at `|Y|+1`, and a chosen zero after it whose tail is
  the largest tail after an entry `< h`. Then `br = 2` and the cut is that zero.
  This covers a final `L_k` (every class), a final `D` with `br = 2`, and a final `W`.
* `cut_br3_gen`: the same for `br = 3`, given that stage 2 does not break.
  `cut_A_succ_br3` (final `A_(k+1)`) and `cut_W_D_br3` (final `D` after `W⌢U`, `U` a word
  of `D`/`V`) supply stage 2 from the token shape.
* `fs_L_root_tok`: the token form of the root class of a final `L_(k+1)`:
  `P⌢w⌢L_(k+1) [n] = (0,0)⌢((2,1,0,2)⌢w⌢(0,1^k,0))^n` when `w` has no `Z`, no `V` and
  every `L_j` in `w` has `j ≥ k+1`.
* `cut_A0_tok`, `fs_A0_tok`: a final `A0` (from `TokenCut.cut_A0`).
-/

namespace SSOS.Seq

/-! ## Finishing `br = 2` and `br = 3` from a low entry -/

theorem br_cut_two_of_low (S : Sequence) (q r : ℕ) (hL : 2 ≤ S.length) (hq : p S 2 = q)
    (hm : mbp S q = r) (hqr : q < r) (he : entry S r ≤ entry S q) :
    br S = 2 ∧ cut S = r := by
  have hf : fbp S 2 = r := by simp only [fbp, hq, hm]
  have hb : breakAt S 2 :=
    breakAt_two_of_low S r (by rw [hq]; exact hqr) (by rw [hf]) (by rw [hq]; exact he)
  have hbr := br_eq_two_of_breakAt S hL hb
  exact ⟨hbr, by rw [cut, hbr, hf]⟩

theorem br_cut_three_of_low (S : Sequence) (q r j : ℕ) (hL : 3 ≤ S.length)
    (h2 : ¬breakAt S 2) (hq : p S 3 = q) (hm : mbp S q = r) (hqj : q < j) (hjr : j ≤ r)
    (he : entry S j ≤ entry S q) : br S = 3 ∧ cut S = r := by
  have hf : fbp S 3 = r := by simp only [fbp, hq, hm]
  have hb : breakAt S 3 :=
    breakAt_of_low S 3 j (by rw [hq]; exact hqj) (by rw [hf]; exact hjr) (by rw [hq]; exact he)
  have hbr := br_eq_three S hL h2 hb
  exact ⟨hbr, by rw [cut, hbr, hf]⟩

/-- The entry at a zero listed by a split of the chosen block. -/
theorem entry_zero_of_split (S Y D M D1 D2 : List ℕ) (c e : ℕ)
    (hS : S = Y ++ (c :: D ++ e :: M)) (hsp : D ++ [e] = D1 ++ 0 :: D2) :
    entry S (Y.length + D1.length + 2) = 0 ∧ D1.length ≤ D.length := by
  have hlen : D.length + 1 = D1.length + 1 + D2.length := by
    have := congrArg List.length hsp; simp at this; omega
  have hS' : S = Y ++ (c :: (D1 ++ 0 :: (D2 ++ M))) := by
    have : D ++ e :: M = D1 ++ 0 :: (D2 ++ M) := by
      have := congrArg (· ++ M) hsp; simpa using this
    rw [hS]; simp [this]
  refine ⟨?_, by omega⟩
  rw [entry_at S Y _ (D1.length + 1) _ hS' (by omega) (by simp)]
  simp [List.getElem_append_right]

/-! ## The general `br = 2` law of a last unit `0⌢M'⌢h` -/

/-- `S = Y⌢c⌢A⌢0⌢M'⌢h`: `p 1` is the head of the last unit (`hM`), `p 2 = |Y|+1`
(`hlt`, `hgap`). The same `S` is `Y⌢c⌢D⌢0⌢M0⌢h` (`hdec`), and no entry `< h` from `c` on
is followed by a tail above `M0⌢h` (`hT`). Then `br = 2` and the cut is that zero. -/
theorem cut_unit_br2 (Y A M' D M0 : List ℕ) (c h : ℕ) (hh : 0 < h)
    (hM : GeAll [h] M' [h])
    (hlt : c :: (A ++ 0 :: (M' ++ [h])) < 0 :: (M' ++ [h]))
    (hgap : GeAll (0 :: (M' ++ [h])) A (0 :: (M' ++ [h])))
    (hdec : A ++ 0 :: M' = D ++ 0 :: M0)
    (hT : TailsLe h (M0 ++ [h]) (c :: D ++ 0 :: (M0 ++ [h])) []) :
    let S := Y ++ c :: A ++ 0 :: (M' ++ [h])
    p S 1 = Y.length + A.length + 2 ∧ p S 2 = Y.length + 1 ∧ br S = 2 ∧
      cut S = Y.length + D.length + 2 := by
  intro S
  have hdec' : A ++ 0 :: (M' ++ [h]) = D ++ 0 :: (M0 ++ [h]) := by
    have := congrArg (· ++ [h]) hdec; simpa using this
  have hS2 : S = Y ++ ((c :: D) ++ 0 :: (M0 ++ [h])) := by
    simp only [S, List.append_assoc, List.cons_append, hdec']
  have hL : S.length = Y.length + A.length + M'.length + 3 := by simp [S]; omega
  have hh' : entry S S.length = h := entry_last S (Y ++ c :: A ++ 0 :: M') h (by simp [S])
  have hp1 : p S 1 = Y.length + A.length + 2 := by
    rw [p_one_eq_sp, hL]
    exact sp_dec S (Y ++ c :: A) M' [h] 0 _ _ (by simp [S]) (by simp; omega) (by simp; omega)
      (cons_lt_of_lt _ _ _ _ hh) hM
  have hp2 : p S 2 = Y.length + 1 := by
    rw [p_succ, hp1]
    exact sp_dec S Y A (0 :: (M' ++ [h])) c _ _ (by simp [S]) (by simp) rfl hlt hgap
  have hm : mbp S (Y.length + 1) = Y.length + D.length + 2 :=
    mbp_dec S Y (c :: D) (M0 ++ [h]) 0 h _ _ hS2 rfl (by simp; omega) (by simp) hh' hh
      (by simpa using hT)
  have he : entry S (Y.length + D.length + 2) = 0 := by
    rw [entry_at S Y _ (D.length + 1) _ hS2 (by omega) (by simp)]
    simp [List.getElem_append_right]
  have := br_cut_two_of_low S _ _ (by omega) hp2 hm (by omega) (by rw [he]; omega)
  exact ⟨hp1, hp2, this⟩

theorem fs_unit_br2 (Y A M' D M0 : List ℕ) (c h : ℕ) (hh : 0 < h)
    (hM : GeAll [h] M' [h])
    (hlt : c :: (A ++ 0 :: (M' ++ [h])) < 0 :: (M' ++ [h]))
    (hgap : GeAll (0 :: (M' ++ [h])) A (0 :: (M' ++ [h])))
    (hdec : A ++ 0 :: M' = D ++ 0 :: M0)
    (hT : TailsLe h (M0 ++ [h]) (c :: D ++ 0 :: (M0 ++ [h])) []) (n : ℕ) :
    fs (Y ++ c :: A ++ 0 :: (M' ++ [h])) n = Y ++ c :: D ++ [0] ++ copies (M0 ++ [h-1]) n := by
  have hc := (cut_unit_br2 Y A M' D M0 c h hh hM hlt hgap hdec hT).2.2.2
  have hdec' : A ++ 0 :: (M' ++ [h]) = D ++ 0 :: (M0 ++ [h]) := by
    have := congrArg (· ++ [h]) hdec; simpa using this
  exact fs_of_cut_word _ (Y ++ c :: D ++ [0]) M0 h
    (by simp only [List.append_assoc, List.cons_append, hdec', List.nil_append]) hh (by rw [hc]; simp; omega) n

/-! ### Instances: final `L_(k+1)`, final `D`, final `W` -/

/-- Final `L_(k+1)` (every class: the root `0` at position 2, an earlier lower unit's
zero, or the head of the last unit). -/
theorem fs_L_gen (Y A D M0 : List ℕ) (c k : ℕ)
    (hlt : c :: (A ++ 0 :: copies [1] (k+1)) < 0 :: copies [1] (k+1))
    (hgap : GeAll (0 :: copies [1] (k+1)) A (0 :: copies [1] (k+1)))
    (hdec : A ++ 0 :: copies [1] k = D ++ 0 :: M0)
    (hT : TailsLe 1 (M0 ++ [1]) (c :: D ++ 0 :: (M0 ++ [1])) []) (n : ℕ) :
    cut (Y ++ c :: A ++ 0 :: copies [1] (k+1)) = Y.length + D.length + 2 ∧
    fs (Y ++ c :: A ++ 0 :: copies [1] (k+1)) n = Y ++ c :: D ++ [0] ++ copies (M0 ++ [0]) n := by
  have hM : ∀ x ∈ copies [1] k, 1 ≤ x := fun x hx => by
    simp only [copies, List.mem_flatten, List.mem_replicate] at hx
    obtain ⟨l, ⟨_, rfl⟩, hx⟩ := hx
    simp at hx; omega
  rw [copies_succ'] at hlt hgap ⊢
  exact ⟨(cut_unit_br2 Y A (copies [1] k) D M0 c 1 (by decide) (geAll_one_of_pos _ hM) hlt
    hgap hdec hT).2.2.2,
    fs_unit_br2 Y A (copies [1] k) D M0 c 1 (by decide) (geAll_one_of_pos _ hM) hlt hgap hdec
      hT n⟩

/-- Final `D` with `br = 2`. -/
theorem fs_D_gen (Y A D M0 : List ℕ) (c : ℕ)
    (hlt : c :: (A ++ [0,2]) < [0,2]) (hgap : GeAll [0,2] A [0,2])
    (hdec : A ++ [0] = D ++ 0 :: M0)
    (hT : TailsLe 2 (M0 ++ [2]) (c :: D ++ 0 :: (M0 ++ [2])) []) (n : ℕ) :
    br (Y ++ c :: A ++ [0,2]) = 2 ∧
    cut (Y ++ c :: A ++ [0,2]) = Y.length + D.length + 2 ∧
    fs (Y ++ c :: A ++ [0,2]) n = Y ++ c :: D ++ [0] ++ copies (M0 ++ [1]) n := by
  have h := cut_unit_br2 Y A [] D M0 c 2 (by decide) (by simp [GeAll]) hlt hgap hdec hT
  exact ⟨h.2.2.1, h.2.2.2,
    fs_unit_br2 Y A [] D M0 c 2 (by decide) (by simp [GeAll]) hlt hgap hdec hT n⟩

/-- Final `W`. -/
theorem fs_W_gen (Y A D M0 : List ℕ) (c : ℕ)
    (hlt : c :: (A ++ tW) < tW) (hgap : GeAll tW A tW)
    (hdec : A ++ [0,1,2] = D ++ 0 :: M0)
    (hT : TailsLe 1 (M0 ++ [1]) (c :: D ++ 0 :: (M0 ++ [1])) []) (n : ℕ) :
    br (Y ++ c :: A ++ tW) = 2 ∧
    cut (Y ++ c :: A ++ tW) = Y.length + D.length + 2 ∧
    fs (Y ++ c :: A ++ tW) n = Y ++ c :: D ++ [0] ++ copies (M0 ++ [0]) n := by
  have hM : GeAll [1] [1,2] [1] := by simp only [GeAll]; decide
  have h := cut_unit_br2 Y A [1,2] D M0 c 1 (by decide) hM hlt hgap hdec hT
  exact ⟨h.2.2.1, h.2.2.2,
    fs_unit_br2 Y A [1,2] D M0 c 1 (by decide) hM hlt hgap hdec hT n⟩

/-- Final `A0`: after every prefix, the cut is right after the head of the last `A0`. -/
theorem cut_A0_tok (Y : List ℕ) :
    br (Y ++ tA 0) = 2 ∧ cut (Y ++ tA 0) = Y.length + 2 := by
  have h := cut_A0 Y
  simpa [tA, copies] using And.intro h.2.2.1 h.2.2.2

theorem fs_A0_tok (Y : List ℕ) (n : ℕ) :
    fs (Y ++ tA 0) n = Y ++ [0,1] ++ copies [1] n := by
  simpa [tA, copies] using fs_A0 Y n

/-! ## The general `br = 3` law -/

/-- `S = Y⌢c⌢A⌢B` with `p 2 = |Y|+|A|+2` (the head of `B`) and stage 2 not breaking;
`p 3 = |Y|+1` (`hlt`, `hgap`); `S = Y⌢c⌢D⌢e⌢M` with the chosen entry `e` and the largest
tail `M` after an entry below the last entry (`hT`); a zero in `D⌢e` (`hlow`). -/
theorem cut_br3_gen (S Y A B D M : List ℕ) (c e : ℕ)
    (hS : S = Y ++ c :: (A ++ B)) (hS' : S = Y ++ (c :: D ++ e :: M)) (hM : M ≠ [])
    (h2 : ¬breakAt S 2) (hp2 : p S 2 = Y.length + A.length + 2)
    (hlt : c :: (A ++ B) < B) (hgap : GeAll B A B)
    (he : e < entry S S.length) (hT : TailsLe (entry S S.length) M (c :: D ++ e :: M) [])
    (hlow : ∃ D1 D2, D ++ [e] = D1 ++ 0 :: D2) :
    br S = 3 ∧ cut S = Y.length + D.length + 2 := by
  have hL : S.length = Y.length + D.length + 2 + M.length := by rw [hS']; simp; omega
  have hMl : 1 ≤ M.length := List.length_pos_iff.mpr hM
  have hp3 : p S 3 = Y.length + 1 := by
    rw [p_succ, hp2]
    exact sp_dec S Y A B c _ _ hS rfl rfl hlt hgap
  have hm : mbp S (Y.length + 1) = Y.length + D.length + 2 :=
    mbp_dec S Y (c :: D) M e _ _ _ hS' rfl (by simp; omega) hM rfl he (by simpa using hT)
  obtain ⟨D1, D2, hsp⟩ := hlow
  obtain ⟨hz, hD1⟩ := entry_zero_of_split S Y D M D1 D2 c e hS' hsp
  exact br_cut_three_of_low S _ _ (Y.length + D1.length + 2) (by omega) h2 hp3 hm (by omega)
    (by omega) (by rw [hz]; omega)

/-- Final `A_(k+1)` (`br = 3`): stage 2 comes from `stage2_A`. -/
theorem cut_A_succ_br3 (Y A D M0 : List ℕ) (c e k : ℕ) (he : e < 2)
    (hlt : c :: (A ++ tA (k+1)) < tA (k+1))
    (hgap : GeAll (tA (k+1)) A (tA (k+1)))
    (hdec : A ++ tA k ++ [0] = D ++ e :: M0)
    (hT : TailsLe 2 (M0 ++ [2]) (c :: D ++ e :: (M0 ++ [2])) [])
    (hlow : ∃ D1 D2, D ++ [e] = D1 ++ 0 :: D2) (n : ℕ) :
    br (Y ++ c :: A ++ tA (k+1)) = 3 ∧
    cut (Y ++ c :: A ++ tA (k+1)) = Y.length + D.length + 2 ∧
    fs (Y ++ c :: A ++ tA (k+1)) n = Y ++ c :: D ++ [e] ++ copies (M0 ++ [1]) n := by
  set S := Y ++ c :: A ++ tA (k+1) with hSdef
  have hst := stage2_A (Y ++ c :: A) k
  have hA1 : tA (k+1) = tA k ++ [0] ++ [2] := by simp [tA, copies_succ']
  have hdec' : A ++ tA (k+1) = D ++ e :: (M0 ++ [2]) := by
    rw [hA1]; have := congrArg (· ++ [2]) hdec; simpa using this
  have hS' : S = Y ++ (c :: D ++ e :: (M0 ++ [2])) := by
    simp only [S, List.append_assoc, List.cons_append, hdec']
  have hlast : entry S S.length = 2 := by
    rw [hS']; exact entry_last _ (Y ++ c :: D ++ e :: M0) 2 (by simp)
  have h := cut_br3_gen S Y A (tA (k+1)) D (M0 ++ [2]) c e (by simp [S]) hS' (by simp)
    hst.2.2 (by rw [hst.1]; simp; omega) hlt hgap (by rw [hlast]; exact he)
    (by rw [hlast]; exact hT) hlow
  refine ⟨h.1, h.2, ?_⟩
  exact fs_of_cut_word S (Y ++ c :: D ++ [e]) M0 2 (by rw [hS']; simp) (by decide)
    (by rw [h.2]; simp; omega) n

/-- Stage 2 of a final `D` after `W⌢U`: `p 2` is the head of `W`, its record is the `1`
after it, and stage 2 does not break. -/
theorem stage2_W_D (X U : List ℕ) (hU0 : ∃ U', U ++ [0,2] = 0 :: U')
    (hU1 : GeAll [0,2] U [0,2])
    (hU2 : TailsLe 2 (2 :: 1 :: (U ++ [0,2])) U [0,2]) :
    let S := X ++ tW ++ U ++ [0,2]
    p S 2 = X.length + 1 ∧ ¬breakAt S 2 := by
  intro S
  have hL : S.length = X.length + U.length + 6 := by simp [S, tW]; omega
  have hh : entry S S.length = 2 := entry_last S (X ++ tW ++ U ++ [0]) 2 (by simp [S])
  have hp1 : p S 1 = X.length + U.length + 5 := by
    have h := p_one_final_D (X ++ tW ++ U)
    simp only [S] at *
    rw [h]; simp [tW]; omega
  have hp2 : p S 2 = X.length + 1 := by
    rw [p_succ, hp1]
    refine sp_dec S X ([1,2,1] ++ U) [0,2] 0 _ _ (by simp [S, tW]) (by simp; omega) rfl
      (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)) ?_
    rw [geAll_append]
    refine ⟨?_, hU1⟩
    simp only [GeAll, List.cons_append, List.nil_append]
    exact ⟨cons_le_of_lt _ _ _ _ (by decide), cons_le_of_lt _ _ _ _ (by decide),
      cons_le_of_lt _ _ _ _ (by decide), trivial⟩
  have hm1 : mbp S (X.length + U.length + 5) = X.length + U.length + 5 :=
    mbp_dec S (X ++ tW ++ U) [] [2] 0 2 _ _ (by simp [S]) (by simp [tW]; omega)
      (by simp [tW]; omega) (by simp) hh (by decide) (by simp [TailsLe])
  have hm2 : mbp S (X.length + 1) = X.length + 2 := by
    refine mbp_dec S X [0] (2 :: 1 :: (U ++ [0,2])) 1 2 _ _ (by simp [S, tW]) rfl rfl
      (by simp) hh (by decide) ?_
    obtain ⟨U', hU'⟩ := hU0
    simp only [TailsLe, List.cons_append, List.nil_append, List.append_nil]
    refine ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide), fun _ => le_rfl, by omega,
      fun _ => by rw [hU']; exact cons_le_of_lt _ _ _ _ (by decide), ?_⟩
    rw [tailsLe_append]
    refine ⟨hU2, ?_⟩
    simp only [TailsLe]
    exact ⟨fun _ => cons_le_cons_same 2 _ _ (nil_le_list _), by omega, trivial⟩
  have hf1 : fbp S 1 = X.length + U.length + 5 := by simp only [fbp, hp1, hm1]
  have hf2 : fbp S 2 = X.length + 2 := by simp only [fbp, hp2, hm2]
  refine ⟨hp2, ?_⟩
  rw [breakAt_iff S (by omega) 2 (by omega)]
  rintro (h | ⟨j, hpj, hj, he⟩)
  · simp only [show (2:ℕ) - 1 = 1 by rfl, hf1, hf2] at h; omega
  · rw [hp2] at hpj he
    rw [hf2] at hj
    obtain rfl : j = X.length + 2 := by omega
    have h1 : entry S (X.length + 2) = 1 :=
      entry_at S X (tW ++ U ++ [0,2]) 1 _ (by simp [S]) rfl (by simp [tW])
    have h0 : entry S (X.length + 1) = 0 :=
      entry_at S X (tW ++ U ++ [0,2]) 0 _ (by simp [S]) rfl (by simp [tW])
    omega

/-- Final `D` after `W⌢U` (`U` a `D`/`V` word, `br = 3`). -/
theorem cut_W_D_br3 (Y A U D M0 : List ℕ) (c e : ℕ) (he : e < 2)
    (hU0 : ∃ U', U ++ [0,2] = 0 :: U')
    (hU1 : GeAll [0,2] U [0,2])
    (hU2 : TailsLe 2 (2 :: 1 :: (U ++ [0,2])) U [0,2])
    (hlt : c :: (A ++ (tW ++ U ++ [0,2])) < tW ++ U ++ [0,2])
    (hgap : GeAll (tW ++ U ++ [0,2]) A (tW ++ U ++ [0,2]))
    (hdec : A ++ tW ++ U ++ [0] = D ++ e :: M0)
    (hT : TailsLe 2 (M0 ++ [2]) (c :: D ++ e :: (M0 ++ [2])) [])
    (hlow : ∃ D1 D2, D ++ [e] = D1 ++ 0 :: D2) (n : ℕ) :
    br (Y ++ c :: A ++ tW ++ U ++ [0,2]) = 3 ∧
    cut (Y ++ c :: A ++ tW ++ U ++ [0,2]) = Y.length + D.length + 2 ∧
    fs (Y ++ c :: A ++ tW ++ U ++ [0,2]) n = Y ++ c :: D ++ [e] ++ copies (M0 ++ [1]) n := by
  set S := Y ++ c :: A ++ tW ++ U ++ [0,2] with hSdef
  have hst := stage2_W_D (Y ++ c :: A) U hU0 hU1 hU2
  have hdec' : A ++ (tW ++ U ++ [0,2]) = D ++ e :: (M0 ++ [2]) := by
    have := congrArg (· ++ [2]) hdec; simpa using this
  have hS' : S = Y ++ (c :: D ++ e :: (M0 ++ [2])) := by
    have h' : c :: D ++ e :: (M0 ++ [2]) = c :: (A ++ (tW ++ U ++ [0,2])) := by
      rw [List.cons_append, hdec']
    rw [h']; simp [S]
  have hlast : entry S S.length = 2 := by
    rw [hS']; exact entry_last _ (Y ++ c :: D ++ e :: M0) 2 (by simp)
  have h := cut_br3_gen S Y A (tW ++ U ++ [0,2]) D (M0 ++ [2]) c e (by simp [S]) hS'
    (by simp) hst.2 (by rw [hst.1]; simp; omega) hlt hgap (by rw [hlast]; exact he)
    (by rw [hlast]; exact hT) hlow
  refine ⟨h.1, h.2, ?_⟩
  exact fs_of_cut_word S (Y ++ c :: D ++ [e]) M0 2 (by rw [hS']; simp) (by decide)
    (by rw [h.2]; simp; omega) n

/-! ## Token form of the root class of a final `L_(k+1)` -/

/-- The tokens after `P`. `L 0` has the raw word of `Z`. -/
inductive Tk43
  | Z | L (j : ℕ) | A (k : ℕ) | W | D | V
  deriving DecidableEq

def Tk43.raw : Tk43 → List ℕ
  | .Z => [0]
  | .L j => 0 :: copies [1] j
  | .A k => tA k
  | .W => tW
  | .D => [0,2]
  | .V => tV

def tkWord (w : List Tk43) : List ℕ := (w.map Tk43.raw).flatten

@[simp] theorem tkWord_nil : tkWord [] = [] := rfl
@[simp] theorem tkWord_cons (t : Tk43) (w : List Tk43) : tkWord (t :: w) = t.raw ++ tkWord w := by
  simp [tkWord]

/-- A token before a final `L_(k+1)` in the root class: no `Z`, no `V`, `L_j` with `j ≥ k+1`. -/
def RootOK (k : ℕ) (t : Tk43) : Prop := t ≠ .Z ∧ t ≠ .V ∧ ∀ j, t = .L j → k+1 ≤ j

theorem tk_raw_head (t : Tk43) : ∃ r, t.raw = 0 :: r := by
  cases t with
  | Z => exact ⟨[], rfl⟩
  | L j => exact ⟨_, rfl⟩
  | A k => exact ⟨[1,2] ++ copies [0,2] k, by simp [Tk43.raw, tA]⟩
  | W => exact ⟨[1,2,1], rfl⟩
  | D => exact ⟨[2], rfl⟩
  | V => exact ⟨[2,1], rfl⟩

theorem tkWord_head (w : List Tk43) (C : List ℕ) (hC : C = [] ∨ ∃ C', C = 0 :: C') :
    tkWord w ++ C = [] ∨ ∃ C', tkWord w ++ C = 0 :: C' := by
  cases w with
  | nil => simpa using hC
  | cons t w =>
    obtain ⟨r, hr⟩ := tk_raw_head t
    exact Or.inr ⟨r ++ tkWord w ++ C, by simp [hr]⟩

theorem root_head_le (k : ℕ) (R : List ℕ) : 0 :: copies [1] (k+1) ≤ 0 :: 1 :: 2 :: R := by
  cases k with
  | zero => simpa [copies] using lex_le_append [0,1] (2 :: R)
  | succ k =>
    rw [copies_succ, copies_succ]
    exact cons_le_cons_same 0 _ _ (cons_le_cons_same 1 _ _ (cons_le_of_lt _ _ _ _ (by decide)))

theorem geAll_of_pos (B' T C : List ℕ) (hT : ∀ x ∈ T, 1 ≤ x) : GeAll (0 :: B') T C := by
  induction T with
  | nil => simp [GeAll]
  | cons x T ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hT
    exact ⟨cons_le_of_lt _ _ _ _ (by omega), ih hT.2⟩

theorem ones_pos (j : ℕ) : ∀ x ∈ copies [1] j, 1 ≤ x := fun x hx => by
  simp only [copies, List.mem_flatten, List.mem_replicate] at hx
  obtain ⟨l, ⟨_, rfl⟩, hx⟩ := hx
  simp at hx; omega

theorem tok_geAll_root (k : ℕ) (t : Tk43) (ht : RootOK k t) (C : List ℕ) :
    GeAll (0 :: copies [1] (k+1)) t.raw C := by
  obtain ⟨hZ, hV, hL⟩ := ht
  cases t with
  | Z => exact absurd rfl hZ
  | V => exact absurd rfl hV
  | L j =>
    obtain ⟨d, rfl⟩ : ∃ d, j = (k+1) + d := ⟨j - (k+1), by have := hL j rfl; omega⟩
    refine ⟨?_, geAll_of_pos _ _ _ (ones_pos _)⟩
    rw [copies_add [1] (k+1) d, List.append_assoc]
    exact cons_le_cons_same 0 _ _ (lex_le_append _ _)
  | A k' =>
    have hB : 0 :: copies [1] (k+1) = 0 :: 1 :: copies [1] k := by rw [copies_succ]; rfl
    simp only [Tk43.raw, tA]
    rw [geAll_append]
    refine ⟨?_, by rw [hB]; exact geAll_copies_02_gen _ _ _⟩
    simp only [GeAll, List.cons_append, List.nil_append]
    exact ⟨root_head_le k _, cons_le_of_lt _ _ _ _ (by decide),
      cons_le_of_lt _ _ _ _ (by decide), trivial⟩
  | W =>
    simp only [Tk43.raw, tW, GeAll, List.cons_append, List.nil_append]
    exact ⟨root_head_le k _, cons_le_of_lt _ _ _ _ (by decide),
      cons_le_of_lt _ _ _ _ (by decide), cons_le_of_lt _ _ _ _ (by decide), trivial⟩
  | D =>
    rw [copies_succ]
    simp only [Tk43.raw, GeAll, List.cons_append, List.nil_append]
    exact ⟨cons_le_cons_same 0 _ _ (cons_le_of_lt _ _ _ _ (by decide)),
      cons_le_of_lt _ _ _ _ (by decide), trivial⟩

theorem word_geAll_root (k : ℕ) (w : List Tk43) (hw : ∀ t ∈ w, RootOK k t) (C : List ℕ) :
    GeAll (0 :: copies [1] (k+1)) (tkWord w) C := by
  induction w with
  | nil => simp [GeAll]
  | cons t w ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hw
    rw [tkWord_cons, geAll_append]
    exact ⟨tok_geAll_root k t hw.1 _, ih hw.2⟩

theorem two_le_two_one (N C : List ℕ) (hC : C = [] ∨ ∃ C', C = 0 :: C') :
    2 :: C ≤ 2 :: 1 :: N := by
  rcases hC with rfl | ⟨C', rfl⟩
  · exact cons_le_cons_same 2 _ _ (nil_le_list _)
  · exact cons_le_cons_same 2 _ _ (cons_le_of_lt _ _ _ _ (by decide))

theorem copies02_tails_root (N : List ℕ) (j : ℕ) (C : List ℕ)
    (hC : C = [] ∨ ∃ C', C = 0 :: C') : TailsLe 1 (2 :: 1 :: N) (copies [0,2] j) C := by
  induction j with
  | zero => simp [copies, TailsLe]
  | succ j ih =>
    rw [copies_succ, tailsLe_append]
    refine ⟨?_, ih⟩
    simp only [TailsLe, List.cons_append, List.nil_append]
    refine ⟨fun _ => two_le_two_one N _ ?_, by omega, trivial⟩
    cases j with
    | zero => simpa [copies] using hC
    | succ j => exact Or.inr ⟨_, by rw [copies_succ]; rfl⟩

theorem tok_tails_root (k : ℕ) (N : List ℕ) (t : Tk43) (ht : RootOK k t) (C : List ℕ)
    (hC : C = [] ∨ ∃ C', C = 0 :: C') : TailsLe 1 (2 :: 1 :: N) t.raw C := by
  obtain ⟨hZ, hV, hL⟩ := ht
  cases t with
  | Z => exact absurd rfl hZ
  | V => exact absurd rfl hV
  | L j =>
    obtain ⟨d, rfl⟩ : ∃ d, j = d + 1 := ⟨j - 1, by have := hL j rfl; omega⟩
    refine ⟨fun _ => ?_, tailsLe_of_ge _ _ _ _ (ones_pos _)⟩
    rw [copies_succ]
    exact cons_le_of_lt _ _ _ _ (by decide)
  | A k' =>
    simp only [Tk43.raw, tA]
    rw [tailsLe_append]
    refine ⟨?_, copies02_tails_root N k' C hC⟩
    simp only [TailsLe, List.cons_append, List.nil_append]
    exact ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide), by omega, by omega, trivial⟩
  | W =>
    simp only [Tk43.raw, tW, TailsLe, List.cons_append, List.nil_append]
    exact ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide), by omega, by omega, by omega, trivial⟩
  | D =>
    simp only [Tk43.raw, TailsLe, List.cons_append, List.nil_append]
    exact ⟨fun _ => two_le_two_one N C hC, by omega, trivial⟩

theorem word_tails_root (k : ℕ) (N : List ℕ) (w : List Tk43) (hw : ∀ t ∈ w, RootOK k t)
    (C : List ℕ) (hC : C = [] ∨ ∃ C', C = 0 :: C') :
    TailsLe 1 (2 :: 1 :: N) (tkWord w) C := by
  induction w with
  | nil => simp [TailsLe]
  | cons t w ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hw
    rw [tkWord_cons, tailsLe_append]
    exact ⟨tok_tails_root k N t hw.1 _ (tkWord_head w C hC), ih hw.2⟩

/-- Root class of a final `L_(k+1)`: when no token of `w` is `Z` or `V` and every `L_j` in
`w` has `j ≥ k+1`, the cut is the second `0` of `P`:
`P⌢w⌢L_(k+1) [n] = (0,0)⌢((2,1,0,2)⌢w⌢(0,1^k,0))^n`. -/
theorem fs_L_root_tok (w : List Tk43) (k n : ℕ) (hw : ∀ t ∈ w, RootOK k t) :
    cut ([0,0,2,1,0,2] ++ tkWord w ++ 0 :: copies [1] (k+1)) = 2 ∧
    fs ([0,0,2,1,0,2] ++ tkWord w ++ 0 :: copies [1] (k+1)) n =
      [0,0] ++ copies ([2,1,0,2] ++ tkWord w ++ 0 :: copies [1] k ++ [0]) n := by
  have hB : 0 :: copies [1] (k+1) = 0 :: 1 :: copies [1] k := by rw [copies_succ]; rfl
  have hlt : (0 : ℕ) :: ([0,2,1,0,2] ++ tkWord w ++ 0 :: copies [1] (k+1)) <
      0 :: copies [1] (k+1) := by
    rw [hB]
    exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)
  have hgap : GeAll (0 :: copies [1] (k+1)) ([0,2,1,0,2] ++ tkWord w)
      (0 :: copies [1] (k+1)) := by
    rw [geAll_append]
    refine ⟨?_, word_geAll_root k w hw _⟩
    rw [hB]
    simp only [GeAll, List.cons_append, List.nil_append]
    exact ⟨cons_le_cons_same 0 _ _ (cons_le_of_lt _ _ _ _ (by decide)),
      cons_le_of_lt _ _ _ _ (by decide), cons_le_of_lt _ _ _ _ (by decide),
      cons_le_cons_same 0 _ _ (cons_le_of_lt _ _ _ _ (by decide)),
      cons_le_of_lt _ _ _ _ (by decide), trivial⟩
  have hdec : [0,2,1,0,2] ++ tkWord w ++ 0 :: copies [1] k =
      [] ++ 0 :: ([2,1,0,2] ++ tkWord w ++ 0 :: copies [1] k) := by simp
  have hRest : tkWord w ++ 0 :: copies [1] (k+1) = [] ∨
      ∃ C', tkWord w ++ 0 :: copies [1] (k+1) = 0 :: C' :=
    tkWord_head w _ (Or.inr ⟨_, rfl⟩)
  have hM : [2,1,0,2] ++ tkWord w ++ 0 :: copies [1] k ++ [1] =
      2 :: 1 :: 0 :: 2 :: (tkWord w ++ 0 :: copies [1] (k+1)) := by
    simp [copies_succ']
  have hT : TailsLe 1 ([2,1,0,2] ++ tkWord w ++ 0 :: copies [1] k ++ [1])
      (0 :: [] ++ 0 :: ([2,1,0,2] ++ tkWord w ++ 0 :: copies [1] k ++ [1])) [] := by
    rw [hM]
    simp only [TailsLe, List.cons_append, List.nil_append, List.append_nil]
    refine ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide), fun _ => le_rfl, by omega, by omega,
      fun _ => two_le_two_one _ _ hRest, by omega, ?_⟩
    rw [tailsLe_append]
    refine ⟨word_tails_root k _ w hw _ (Or.inr ⟨_, rfl⟩), ?_⟩
    simp only [TailsLe]
    refine ⟨fun _ => ?_, tailsLe_of_ge _ _ _ _ (ones_pos _)⟩
    rw [copies_succ, List.append_nil]
    exact cons_le_of_lt _ _ _ _ (by decide)
  have h := fs_L_gen [] ([0,2,1,0,2] ++ tkWord w) [] ([2,1,0,2] ++ tkWord w ++ 0 :: copies [1] k)
    0 k hlt hgap hdec hT n
  simp only [List.nil_append, List.length_nil, List.cons_append] at h
  constructor
  · simpa using h.1
  · simpa using h.2

end SSOS.Seq
