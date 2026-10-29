import SSOS.PrefixCut

/-!
The cut of a terminal run of `W` is independent of the run length after
an `A_d` base and a token word. The proof compares suffix records through the
first `W`; the resulting fundamental-sequence block has a fixed good prefix.
-/

namespace SSOS.Seq

theorem cut_W_run_after_A0 (X : List ℕ) (m : ℕ) :
    cut (X ++ tA 0 ++ copies tW (m + 1)) = cut (X ++ tA 0 ++ tW) := by
  have hm := (law_W_A0 X m).2.2.1
  have h0 := (law_W_A0 X 0).2.2.1
  rw [copies_succ']
  simpa [copies] using hm.trans h0.symm

theorem cut_W_run_after_A_succ (X : List ℕ) (k m : ℕ) :
    cut (X ++ tA (k + 1) ++ copies tW (m + 1)) =
      cut (X ++ tA (k + 1) ++ tW) := by
  have hm := (law_W_A X k m).2.2.1
  have h0 := (law_W_A X k 0).2.2.1
  rw [copies_succ']
  simpa [copies] using hm.trans h0.symm

theorem cut_W_run_after_A (X : List ℕ) (k m : ℕ) :
    cut (X ++ tA k ++ copies tW (m + 1)) = cut (X ++ tA k ++ tW) := by
  cases k with
  | zero => exact cut_W_run_after_A0 X m
  | succ k => exact cut_W_run_after_A_succ X k m

theorem cut_W_run_after_A_D (X : List ℕ) (k r m : ℕ) :
    cut (X ++ tA k ++ copies [0,2] r ++ copies tW (m + 1)) =
      cut (X ++ tA k ++ copies [0,2] r ++ tW) := by
  simpa only [List.append_assoc, tA_append_D_copies] using
    cut_W_run_after_A X (k + r) m

theorem cut_W_run_after_A_D_W (X : List ℕ) (k r q m : ℕ) :
    cut (X ++ tA k ++ copies [0,2] r ++ copies tW q ++ copies tW (m+1)) =
      cut (X ++ tA k ++ copies [0,2] r ++ copies tW q ++ tW) := by
  have h₁ := cut_W_run_after_A_D X k r (q+m)
  have h₂ := cut_W_run_after_A_D X k r q
  rw [show q + m + 1 = q + (m+1) by omega, copies_add] at h₁
  rw [copies_add] at h₂
  have hW1 : copies tW 1 = tW := by simp [copies]
  rw [copies_succ' tW m] at h₁
  rw [hW1] at h₂
  rw [copies_succ' tW m]
  simpa only [List.append_assoc] using h₁.trans h₂.symm

theorem fs_W_run_after_A_D (X : List ℕ) (k r m n : ℕ) :
    fs (X ++ tA k ++ copies [0,2] r ++ copies tW (m+1)) n =
      X ++ copies (tA (k+r) ++ copies tW m) n ++ [0,1,2,0] := by
  simp only [List.append_assoc, tA_append_D_copies, copies_succ']
  cases h : k+r with
  | zero =>
      have hk : k = 0 ∧ r = 0 := by omega
      rcases hk with ⟨rfl, rfl⟩
      simpa [copies, List.append_assoc] using (law_W_A0 X m).2.2.2 n
  | succ j =>
      simpa [h, List.append_assoc] using
        (law_W_A X j m).2.2.2 n

theorem cut_W_run_after_E (X : List ℕ) (m : ℕ) :
    cut (X ++ tE ++ copies tW (m + 1)) = cut (X ++ tE ++ tW) := by
  have hm := (law_W_E X m).2.2.1
  have h0 := (law_W_E X 0).2.2.1
  rw [copies_succ']
  simpa [copies] using hm.trans h0.symm

theorem cut_W_run_after_E_W (X : List ℕ) (q m : ℕ) :
    cut (X ++ tE ++ copies tW q ++ copies tW (m+1)) =
      cut (X ++ tE ++ copies tW q ++ tW) := by
  have h₁ := cut_W_run_after_E X (q+m)
  have h₂ := cut_W_run_after_E X q
  rw [show q + m + 1 = q + (m+1) by omega, copies_add tW q (m+1)] at h₁
  rw [copies_add tW q 1] at h₂
  have hW1 : copies tW 1 = tW := by simp [copies]
  rw [copies_succ' tW m] at h₁
  rw [hW1] at h₂
  rw [copies_succ' tW m]
  simpa only [List.append_assoc] using h₁.trans h₂.symm

theorem tailsLe_mono_threshold (a b : ℕ) (M A B : List ℕ)
    (hab : a ≤ b) (h : TailsLe b M A B) : TailsLe a M A B := by
  induction A generalizing B with
  | nil => trivial
  | cons x xs ih =>
    exact ⟨fun hx => h.1 (by omega), ih B h.2⟩

/-- The `E D^r W^m` unit has the same W cut for every run length. -/
theorem W_hyps_E_D (r m : ℕ) :
    let Q := [0,2,1] ++ copies [0,2] (r+1) ++ copies tW m
    let M := [2,1] ++ copies [0,2] (r+1) ++ copies tW (m+1)
    Q ++ tW = 0 :: M ∧ GeAll tW Q tW ∧
      1 :: 2 :: 0 :: M ≤ M ∧ TailsLe 1 M M [] := by
  intro Q M
  have hlast : ∃ B, copies tW (m+1) = 0 :: B := by
    exact ⟨[1,2,1] ++ copies tW m, by rw [copies_succ]; rfl⟩
  obtain ⟨B, hB⟩ := hlast
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Q, M, ← copies_succ']
  · simp only [Q]
    rw [geAll_append, geAll_append]
    refine ⟨⟨?_, geAll_copies_02 _ _⟩, geAll_copies_W _ _⟩
    simp only [GeAll, List.cons_append, List.nil_append]
    exact ⟨(tW_lt_02 _).le, cons_le_of_lt _ _ _ _ (by decide),
      cons_le_of_lt _ _ _ _ (by decide), trivial⟩
  · simp only [M, List.cons_append, List.nil_append]
    exact cons_le_of_lt _ _ _ _ (by decide)
  · simp only [M]
    rw [tailsLe_append, tailsLe_append]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [TailsLe]
    · rw [hB]
      have h := tailsLe_mono_threshold 1 2
        (2 :: 1 :: (copies [0,2] (r+1) ++ 0 :: B))
        (copies [0,2] (r+1)) (0 :: B) (by omega)
        (tailsLe_copies_02_mid (copies [0,2] (r+1) ++ 0 :: B) (r+1) B)
      simpa only [List.cons_append, List.nil_append, List.append_nil,
        List.append_assoc] using h
    · simpa [List.append_assoc] using
        tailsLe_copies_W_two (m+1)
          (1 :: copies [0,2] (r+1) ++ copies tW (m+1)) []

theorem cut_W_run_after_E_D (X : List ℕ) (r m : ℕ) :
    cut (X ++ tE ++ copies [0,2] (r+1) ++ copies tW (m+1)) =
      cut (X ++ tE ++ copies [0,2] (r+1) ++ tW) := by
  obtain ⟨hm1, hm2, hm3, hm4⟩ := W_hyps_E_D r m
  obtain ⟨h01, h02, h03, h04⟩ := W_hyps_E_D r 0
  have hcutm := (cut_W_core X _ _ hm1 hm2 hm3 hm4).2.2
  have hcut0 := (cut_W_core X _ _ h01 h02 h03 h04).2.2
  have hrewrite : ∀ q : ℕ,
      X ++ [0,1,2] ++ ([0,2,1] ++ copies [0,2] (r+1) ++ copies tW q) ++ tW =
        X ++ tE ++ copies [0,2] (r+1) ++ copies tW (q+1) := by
    intro q
    simp [tE, copies_succ', List.append_assoc]
  rw [hrewrite m] at hcutm
  rw [hrewrite 0] at hcut0
  simpa [copies] using hcutm.trans hcut0.symm

theorem cut_W_run_after_E_D_W (X : List ℕ) (r q m : ℕ) :
    cut (X ++ tE ++ copies [0,2] (r+1) ++ copies tW q ++ copies tW (m+1)) =
      cut (X ++ tE ++ copies [0,2] (r+1) ++ copies tW q ++ tW) := by
  have h₁ := cut_W_run_after_E_D X r (q+m)
  have h₂ := cut_W_run_after_E_D X r q
  rw [show q + m + 1 = q + (m+1) by omega, copies_add tW q (m+1)] at h₁
  rw [copies_add tW q 1] at h₂
  have hW1 : copies tW 1 = tW := by simp [copies]
  rw [copies_succ' tW m] at h₁
  rw [hW1] at h₂
  rw [copies_succ' tW m]
  simpa only [List.append_assoc] using h₁.trans h₂.symm

theorem fs_W_run_after_E_D (X : List ℕ) (r m n : ℕ) :
    fs (X ++ tE ++ copies [0,2] (r+1) ++ copies tW (m+1)) n =
      X ++ copies (tE ++ copies [0,2] (r+1) ++ copies tW m) n ++ [0,1,2,0] := by
  obtain ⟨h1, h2, h3, h4⟩ := W_hyps_E_D r m
  have h := fs_W_core X _ _ h1 h2 h3 h4 n
  simpa [tE, copies_succ', List.append_assoc] using h

/-- A `D` immediately after `A0 W` iterates that `W` in the real expansion. -/
theorem fs_A0_W_D (X : List ℕ) (n : ℕ) :
    fs (X ++ tA 0 ++ tW ++ [0,2]) n =
      X ++ tA 0 ++ copies tW n ++ [0,1] := by
  have hc : cut (X ++ tA 0 ++ tW ++ [0,2]) = (X ++ tA 0).length + 2 := by
    have h := cut_prefix_A0_W_D_run X 0
    rw [cut_A0_W_D_run 0] at h
    simpa [tA, copies, List.append_assoc] using h
  have hS : X ++ tA 0 ++ tW ++ [0,2] =
      (X ++ tA 0 ++ [0,1]) ++ [2,1,0] ++ [2] := by
    simp [tW, List.append_assoc]
  have hcut : cut (X ++ tA 0 ++ tW ++ [0,2]) = (X ++ tA 0 ++ [0,1]).length := by
    simpa [List.length_append, Nat.add_assoc] using hc
  rw [fs_of_cut_word _ (X ++ tA 0 ++ [0,1]) [2,1,0] 2 hS (by decide) hcut n]
  have hr := copies_rotate [2,1] [0,1] n
  simp only [List.append_assoc] at hr ⊢
  simpa [tW, List.append_assoc] using congrArg (fun r => X ++ tA 0 ++ r) hr

/-! A periodic `W D W` block: the first new zero after `W` is the record. -/

def tWDW : List ℕ := tW ++ [0,2] ++ tW

theorem W_le_WDW_run (j : ℕ) : tW ≤ copies tWDW j ++ tW := by
  cases j with
  | zero => simp [copies]
  | succ j =>
      rw [copies_succ]
      simp only [tWDW, List.append_assoc]
      exact lex_le_append tW _

theorem WDW_run_le (j k : ℕ) :
    copies tWDW k ++ tW ≤ copies tWDW (j+k) ++ tW := by
  rw [Nat.add_comm j k, copies_add, List.append_assoc]
  exact append_le_append_left (copies tWDW k) _ _ (W_le_WDW_run j)

theorem geAll_WDW_run (j : ℕ) (B : List ℕ) : GeAll tW (copies tWDW j) B := by
  induction j generalizing B with
  | zero => simp [copies, GeAll]
  | succ j ih =>
      rw [copies_succ, geAll_append]
      refine ⟨?_, ih B⟩
      simp only [tWDW, geAll_append]
      exact ⟨⟨by simpa [copies] using geAll_copies_W 1 _ ,
        by simpa [copies] using geAll_copies_02 1 _⟩,
        by simpa [copies] using geAll_copies_W 1 _⟩

theorem tailsLe_WDW_run (a b : ℕ) :
    TailsLe 1 (2 :: (tW ++ copies tWDW (a+b) ++ tW))
      (copies tWDW b) tW := by
  induction b generalizing a with
  | zero => simp [copies, TailsLe]
  | succ b ih =>
      rw [copies_succ, tailsLe_append]
      refine ⟨?_, ?_⟩
      · change TailsLe 1 (2 :: (tW ++ copies tWDW (a+(b+1)) ++ tW))
          (tW ++ [0,2] ++ tW) (copies tWDW b ++ tW)
        rw [tailsLe_append, tailsLe_append]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · have hW1 : copies tW 1 = tW := by simp [copies]
          simpa only [hW1] using tailsLe_copies_W_two 1
            (tW ++ copies tWDW (a+(b+1)) ++ tW)
            ([0,2] ++ (tW ++ (copies tWDW b ++ tW)))
        · simp only [TailsLe, List.cons_append, List.nil_append]
          refine ⟨?_, by omega, trivial⟩
          intro _
          have hf : copies tWDW b ++ tW ≤ copies tWDW (a+(b+1)) ++ tW := by
            simpa only [show (a+1)+b = a+(b+1) by omega] using WDW_run_le (a+1) b
          have hw := append_le_append_left tW _ _ hf
          exact cons_le_cons_same 2 _ _ (by simpa only [List.append_assoc] using hw)
        · have hW1 : copies tW 1 = tW := by simp [copies]
          simpa only [hW1, List.append_assoc] using tailsLe_copies_W_two 1
            (tW ++ copies tWDW (a+(b+1)) ++ tW)
            (copies tWDW b ++ tW)
      · simpa only [show (a+1)+b = a+(b+1) by omega] using ih (a+1)

theorem tailsLe_WDW_self (a : ℕ) :
    let M := 2 :: (tW ++ copies tWDW a ++ tW)
    TailsLe 1 M M [] := by
  intro M
  have hW1 : copies tW 1 = tW := by simp [copies]
  have hM : M = [2] ++ tW ++ copies tWDW a ++ tW := by
    simp [M, List.append_assoc]
  rw [hM, tailsLe_append, tailsLe_append, tailsLe_append]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp [TailsLe]
  · simpa [M, hW1, List.append_assoc] using tailsLe_copies_W_two 1
      (tW ++ copies tWDW a ++ tW) (copies tWDW a ++ tW)
  · simpa [M, hW1, List.append_assoc] using tailsLe_WDW_run 0 a
  · simpa [M, hW1, List.append_assoc] using tailsLe_copies_W_two 1
      (tW ++ copies tWDW a ++ tW) []

theorem tailsLe_WDW_cut (a : ℕ) :
    let M := 2 :: (tW ++ copies tWDW a ++ tW)
    TailsLe 1 M (tA 0 ++ tW ++ 0 :: M) [] := by
  intro M
  have hW1 : copies tW 1 = tW := by simp [copies]
  rw [tailsLe_append, tailsLe_append]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [tA, copies, TailsLe]
    exact cons_le_of_lt _ _ _ _ (by decide)
  · simpa [M, hW1, List.append_nil] using tailsLe_copies_W_two 1
      (tW ++ copies tWDW a ++ tW) (0 :: M)
  · simp only [TailsLe, List.append_nil]
    exact ⟨fun _ => le_rfl, tailsLe_WDW_self a⟩

theorem cut_WDW_run (X : List ℕ) (a : ℕ) :
    cut (X ++ tA 0 ++ copies tWDW (a+1) ++ tW) = X.length + 8 := by
  let M := 2 :: (tW ++ copies tWDW a ++ tW)
  let S := X ++ tA 0 ++ copies tWDW (a+1) ++ tW
  have hS : S = X ++ ((tA 0 ++ tW) ++ 0 :: M) := by
    simp [S, M, tWDW, copies_succ, List.append_assoc]
  have hp1 : p S 1 = (X ++ tA 0 ++ copies tWDW (a+1)).length + 1 := by
    simpa [S, List.append_assoc] using p_one_final_W (X ++ tA 0 ++ copies tWDW (a+1))
  have hgap : GeAll tW ([1,2] ++ copies tWDW (a+1)) tW := by
    rw [geAll_append]
    refine ⟨?_, geAll_WDW_run _ _⟩
    simp only [GeAll, List.cons_append, List.nil_append]
    exact ⟨cons_le_of_lt _ _ _ _ (by decide),
      cons_le_of_lt _ _ _ _ (by decide), trivial⟩
  have hp2 : p S 2 = X.length + 1 := by
    rw [p_succ, hp1]
    refine sp_dec S X ([1,2] ++ copies tWDW (a+1)) tW 0 _ _
      (by simp [S, tA, copies, List.append_assoc])
      (by simp [tA, copies, List.length_append]; omega) rfl ?_ hgap
    rw [copies_succ]
    simp [tWDW, tW, List.cons_lt_cons_iff]
  have hh : entry S S.length = 1 := by
    exact entry_last S (X ++ tA 0 ++ copies tWDW (a+1) ++ [0,1,2]) 1
      (by simp [S, tW, List.append_assoc])
  have hm2 : mbp S (X.length + 1) = X.length + 8 := by
    refine mbp_dec S X (tA 0 ++ tW) M 0 1 _ _ hS rfl
      (by simp [tA, copies, tW]) (by simp [M]) hh (by decide) ?_
    simpa [M] using tailsLe_WDW_cut a
  have hf2 : fbp S 2 = X.length + 8 := by simp [fbp, hp2, hm2]
  have he1 : entry S (X.length + 1) = 0 := by
    rw [hS]
    simpa [tA, copies] using
      entry_at (X ++ ((tA 0 ++ tW) ++ 0 :: M)) X ((tA 0 ++ tW) ++ 0 :: M)
        0 (X.length+1) rfl rfl (by simp [tA, copies])
  have he8 : entry S (X.length + 8) = 0 := by
    rw [hS]
    have h := entry_at (X ++ ((tA 0 ++ tW) ++ 0 :: M))
      (X ++ tA 0 ++ tW) (0 :: M) 0 (X.length+8)
      (by simp [List.append_assoc]) (by simp [tA, copies, tW]) (by simp)
    simpa [tA, copies, tW] using h
  have hb : breakAt S 2 := breakAt_two_of_low S (X.length+8)
    (by omega) (by rw [hf2]) (by rw [he8, hp2, he1])
  have hL : 2 ≤ S.length := by simp [S, tA, copies, tW]; omega
  have hbr : br S = 2 := br_eq_two_of_breakAt S hL hb
  rw [cut, hbr, fbp, hp2]
  exact hm2

theorem cut_WDW_run_constant (X : List ℕ) (m : ℕ) :
    cut (X ++ tA 0 ++ copies tWDW (m+1) ++ tW) =
      cut (X ++ tA 0 ++ tWDW ++ tW) := by
  have hm := cut_WDW_run X m
  have h0 := cut_WDW_run X 0
  simpa [copies] using hm.trans h0.symm

/-! A suffix floor for a terminal `W`.  It is the order invariant needed by
the general record comparison, including the `W D` cases. -/

def WFloor (R : List ℕ) : Prop :=
  ∀ i, i ≤ R.length → tW ≤ R.drop i ++ tW

theorem WFloor_drop (R : List ℕ) (h : WFloor R) (k : ℕ) (hk : k ≤ R.length) :
    WFloor (R.drop k) := by
  intro i hi
  have hki : k + i ≤ R.length := by
    simp [List.length_drop] at hi
    omega
  simpa only [List.drop_drop, Nat.add_comm] using h (k+i) hki

theorem WFloor_periodic (R : List ℕ) (hs : ZeroSafe R) (hf : WFloor R)
    (m : ℕ) : copies tW (m+1) ≤ R ++ copies tW (m+1) := by
  cases hs with
  | nil => simp
  | one ht =>
      rw [copies_succ]
      exact cons_le_of_lt _ _ _ _ (by decide)
  | two ht =>
      rw [copies_succ]
      exact cons_le_of_lt _ _ _ _ (by decide)
  | zero2 ht =>
      rw [copies_succ]
      apply cons_le_cons_same
      exact cons_le_of_lt _ _ _ _ (by decide)
  | zero12 ht =>
      cases ht with
      | nil =>
          have h0 := hf 0 (by simp)
          have hbad : ([0,1,2] : List ℕ) ++ tW < tW := by
            simp [tW, List.cons_lt_cons_iff]
          exact (not_le_of_gt hbad h0).elim
      | one hu =>
          have ih := WFloor_periodic _ hu
            (by simpa using WFloor_drop _ hf 4 (by simp)) m
          rw [copies_succ]
          apply append_le_append_left tW
          have hprefix : copies tW m ≤ tW ++ copies tW m := by
            calc
              copies tW m ≤ copies tW m ++ tW := lex_le_append _ _
              _ = tW ++ copies tW m := by rw [← copies_succ' tW m, copies_succ]
          rw [copies_succ] at ih
          exact hprefix.trans ih
      | two hu =>
          rw [copies_succ]
          repeat' apply cons_le_cons_same
          exact cons_le_of_lt _ _ _ _ (by decide)
      | zero12 hu =>
          have h0 := hf 0 (by simp)
          exact (not_le_of_gt (by simp [tW, List.cons_lt_cons_iff]) h0).elim
      | zero2 hu =>
          have h0 := hf 0 (by simp)
          exact (not_le_of_gt (by simp [tW, List.cons_lt_cons_iff]) h0).elim
termination_by R.length

theorem WFloor_periodic_strict (R : List ℕ) (hs : ZeroSafe R) (hf : WFloor R)
    (hne : R ≠ []) (m : ℕ) :
    copies tW (m+1) < R ++ copies tW (m+1) := by
  have hle := WFloor_periodic R hs hf m
  have hne' : copies tW (m+1) ≠ R ++ copies tW (m+1) := by
    intro he
    have hl := congrArg List.length he
    simp only [List.length_append] at hl
    have hz : R.length = 0 := by omega
    exact hne (List.length_eq_zero_iff.mp hz)
  exact lt_of_le_of_ne hle hne'

theorem WFloor_cmp_periodic (A B : List ℕ) (hs : ZeroSafe A)
    (hf : WFloor A) (hlen : B.length ≤ A.length) (m : ℕ) :
    (A ++ copies tW (m+1) < B ++ copies tW (m+1)) ↔
      (A ++ tW < B ++ tW) := by
  induction B generalizing A with
  | nil =>
      cases A with
      | nil => simp
      | cons a A =>
          have hlong := WFloor_periodic_strict (a :: A) hs hf (by simp) m
          have hshort := WFloor_periodic_strict (a :: A) hs hf (by simp) 0
          simp [copies] at hlong ⊢
          exact ⟨fun h => (not_lt_of_ge hlong.le h).elim,
            fun h => (not_lt_of_ge hshort.le h).elim⟩
  | cons b B ih =>
      cases A with
      | nil => simp at hlen
      | cons a A =>
          have hst : ZeroSafe A := zeroSafe_tail hs
          have hft : WFloor A := by
            simpa using WFloor_drop (a :: A) hf 1 (by simp)
          have hlen' : B.length ≤ A.length := by simpa using hlen
          by_cases hab : a = b
          · subst b
            simpa [List.cons_lt_cons_iff] using ih A hst hft hlen'
          · by_cases hlt : a < b
            · simp [List.cons_lt_cons_iff, hlt]
            · have hgt : b < a := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hab)
              simp [List.cons_lt_cons_iff, hab, hlt]

theorem WFloor_after_sp_W (Y : List ℕ) (r : ℕ)
    (hr : r = sp (Y ++ tW) (Y.length + 1)) (hrle : r ≤ Y.length) :
    WFloor (Y.drop r) := by
  intro i hi
  by_cases hil : i < (Y.drop r).length
  · have hir : r + i < Y.length := by
      simp [List.length_drop] at hil
      omega
    have hscore : suf (Y ++ tW) (r+i+1) = (Y.drop r).drop i ++ tW := by
      have hd : (Y ++ tW).drop (r+i) = Y.drop (r+i) ++ tW :=
        List.drop_append_of_le_length (by omega)
      simp [suf, hd, List.drop_drop, Nat.add_assoc]
    have hfinal : suf (Y ++ tW) (Y.length + 1) = tW := by
      simpa using suf_app Y tW 0
    by_contra hnot
    have hlt : (Y.drop r).drop i ++ tW < tW := lt_of_not_ge hnot
    have hbound := le_sp (Y ++ tW) (Y.length+1) (r+i+1)
      (by omega) (by omega) (by rw [hscore, hfinal]; exact hlt)
    rw [← hr] at hbound
    omega
  · have heq : i = (Y.drop r).length := by omega
    rw [heq]
    rw [List.drop_length]
    simp

theorem lt_W_append_periodic (R : List ℕ) (hs : ZeroSafe R) (m : ℕ) :
    (R ++ copies tW (m+1) < tW) ↔ (R ++ tW < tW) := by
  cases hs with
  | nil =>
      rw [copies_succ]
      simp [tW]
  | one hs =>
      rw [copies_succ]
      simp [tW, List.cons_lt_cons_iff]
  | two hs =>
      rw [copies_succ]
      simp [tW, List.cons_lt_cons_iff]
  | zero2 hs =>
      rw [copies_succ]
      simp [tW, List.cons_lt_cons_iff]
  | zero12 hs =>
      cases hs <;> rw [copies_succ] <;>
        simp [tW, List.cons_lt_cons_iff]

theorem suf_W_run_at_prefix (Y : List ℕ) (i m : ℕ) (hi : 1 ≤ i)
    (hiY : i ≤ Y.length) :
    suf (Y ++ copies tW (m+1)) i = Y.drop (i-1) ++ copies tW (m+1) := by
  have hd : (Y ++ copies tW (m+1)).drop (i-1) =
      Y.drop (i-1) ++ copies tW (m+1) :=
    List.drop_append_of_le_length (by omega)
  simpa [suf] using hd

theorem sp_W_run_stable (Y : List ℕ) (hs : ZeroSafe Y) (hY : Y ≠ []) (m : ℕ) :
    sp (Y ++ copies tW (m+1)) ((Y ++ copies tW m).length + 1) =
      sp (Y ++ tW) (Y.length + 1) := by
  let S := Y ++ copies tW (m+1)
  let T := Y ++ tW
  let x := (Y ++ copies tW m).length + 1
  let r := sp T (Y.length + 1)
  have hYL : 1 ≤ Y.length := List.length_pos_iff.mpr hY
  have hrle : r ≤ Y.length := by
    have h := sp_lt T (Y.length+1) (by omega)
    simpa [r, T] using h
  have hx : x = Y.length + (copies tW m).length + 1 := by simp [x]
  have hS : S = (Y ++ copies tW m) ++ tW := by
    simp [S, copies_succ', List.append_assoc]
  have hlast : suf S x = tW := by
    rw [hS]
    simpa [x] using suf_app (Y ++ copies tW m) tW 0
  have hlastT : suf T (Y.length+1) = tW := by
    simpa [T] using suf_app Y tW 0
  have hcandidate : ∀ i, 1 ≤ i → i < x →
      (suf S i < suf S x ↔ i ≤ Y.length ∧ suf T i < suf T (Y.length+1)) := by
    intro i hi hix
    by_cases hiY : i ≤ Y.length
    · have hsi := suf_W_run_at_prefix Y i m hi hiY
      have hti := suf_W_run_at_prefix Y i 0 hi hiY
      rw [hlast, hlastT, hsi]
      have hT0 : copies tW (0+1) = tW := by simp [copies]
      rw [hT0] at hti
      have hti' : suf T i = Y.drop (i-1) ++ tW := by simpa [T] using hti
      rw [hti']
      simpa [hiY] using lt_W_append_periodic (Y.drop (i-1))
        (zeroSafe_drop hs (i-1)) m
    · have hYlen : Y.length + 1 ≤ i := by omega
      let k := i - Y.length - 1
      have hk : k < (copies tW m).length := by simp [k, hx] at hix ⊢; omega
      have hik : i = Y.length + k + 1 := by simp [k]; omega
      have hpre : suf S i = (copies tW m).drop k ++ tW := by
        rw [hS, hik]
        have h0 := suf_app Y (copies tW m ++ tW) k
        have hd : (copies tW m ++ tW).drop k =
            (copies tW m).drop k ++ tW :=
          List.drop_append_of_le_length (by omega)
        simp [suf, List.append_assoc, hd] at h0 ⊢
      have hge : tW ≤ suf S i := by
        rw [hpre]
        exact (geAll_spec tW (copies tW m) tW).mp (geAll_copies_W m tW) k hk
      simp [hlast, not_lt_of_ge hge, hiY]
  have hupper : sp S x ≤ r := (sp_le_iff S x r).2 ⟨by
      exact one_le_sp T _, fun i hi hix hlt => by
      have h := (hcandidate i hi hix).mp hlt
      have hsT := h.2
      exact le_sp T (Y.length+1) i hi (by omega) hsT⟩
  have hlower : r ≤ sp S x := by
    rcases sp_origin T (Y.length+1) with he | ⟨hlo, hix, hlt⟩
    · change sp T (Y.length+1) ≤ sp S x
      rw [he]
      exact one_le_sp S x
    · have hcan : suf S r < suf S x :=
        (hcandidate r hlo (by omega)).mpr ⟨hrle, by simpa [r] using hlt⟩
      exact le_sp S x r hlo (by omega) hcan
  exact le_antisymm hupper hlower

theorem lt_W_run_of_tail_floor (a : ℕ) (A : List ℕ)
    (hs : ZeroSafe (a :: A)) (hf : WFloor A) (m : ℕ) :
    ((a :: A) ++ copies tW (m+1) < copies tW (m+1)) ↔
      ((a :: A) ++ tW < tW) := by
  by_cases hlt : (a :: A) ++ tW < tW
  · have hlt' := (lt_W_append_periodic (a :: A) hs m).mpr hlt
    have hW : tW ≤ copies tW (m+1) := by
      rw [copies_succ]
      exact lex_le_append tW _
    exact ⟨fun _ => hlt, fun _ => lt_of_lt_of_le hlt' hW⟩
  · have hbase : tW ≤ (a :: A) ++ tW := le_of_not_gt hlt
    have hfull : WFloor (a :: A) := by
      intro i hi
      cases i with
      | zero => simpa using hbase
      | succ i =>
          have hiA : i ≤ A.length := by simp at hi; omega
          simpa using hf i hiA
    have hge := WFloor_periodic (a :: A) hs hfull m
    exact ⟨fun h => (not_lt_of_ge hge h).elim, fun h => (hlt h).elim⟩

theorem suf_W_run_after_Y (Y : List ℕ) (i m : ℕ) (hi : i ≤ Y.length) :
    suf (Y ++ copies tW (m+1)) (i+1) = Y.drop i ++ copies tW (m+1) := by
  have hd : (Y ++ copies tW (m+1)).drop i = Y.drop i ++ copies tW (m+1) :=
    List.drop_append_of_le_length hi
  simpa [suf] using hd

theorem score_lt_W_run_stable (Y : List ℕ) (hs : ZeroSafe Y)
    (r i j m : ℕ) (hf : WFloor (Y.drop r))
    (hri : r ≤ i) (hij : i < j) (hjY : j ≤ Y.length) :
    (suf (Y ++ copies tW (m+1)) (i+1) <
      suf (Y ++ copies tW (m+1)) (j+1)) ↔
      (suf (Y ++ tW) (i+1) < suf (Y ++ tW) (j+1)) := by
  have hiY : i ≤ Y.length := by omega
  have hfi : WFloor (Y.drop i) := by
    have hd : (Y.drop r).drop (i-r) = Y.drop i := by
      rw [List.drop_drop, show r + (i-r) = i by omega]
    rw [← hd]
    exact WFloor_drop (Y.drop r) hf (i-r) (by simp [List.length_drop]; omega)
  have hlen : (Y.drop j).length ≤ (Y.drop i).length := by
    simp [List.length_drop]
    omega
  have h := WFloor_cmp_periodic (Y.drop i) (Y.drop j)
    (zeroSafe_drop hs i) hfi hlen m
  rw [suf_W_run_after_Y Y i m hiY, suf_W_run_after_Y Y j m hjY]
  have hi0 : suf (Y ++ tW) (i+1) = Y.drop i ++ tW := by
    simpa [copies] using suf_W_run_after_Y Y i 0 hiY
  have hj0 : suf (Y ++ tW) (j+1) = Y.drop j ++ tW := by
    simpa [copies] using suf_W_run_after_Y Y j 0 hjY
  rw [hi0, hj0]
  exact h

theorem score_lt_first_W_stable (A : List ℕ) (hs : ZeroSafe (0 :: A))
    (hf : WFloor A) (m : ℕ) :
    (A ++ copies tW (m+1) < [1,2,1] ++ copies tW m) ↔
      (A ++ tW < [1,2,1]) := by
  have h := lt_W_run_of_tail_floor 0 A hs hf m
  rw [copies_succ] at h
  rw [copies_succ]
  simpa [tW, List.cons_lt_cons_iff, List.append_assoc] using h

theorem score_lt_first_W_at_Y (Y : List ℕ) (hs : ZeroSafe Y)
    (r i m : ℕ) (hf : WFloor (Y.drop r)) (hri : r ≤ i)
    (hi : 1 ≤ i) (hiY : i ≤ Y.length) (hz : Y[i-1] = 0) :
    (suf (Y ++ copies tW (m+1)) (i+1) <
      suf (Y ++ copies tW (m+1)) (Y.length+2)) ↔
      (suf (Y ++ tW) (i+1) < suf (Y ++ tW) (Y.length+2)) := by
  have hR : Y.drop (i-1) = 0 :: Y.drop i := by
    rw [List.drop_eq_getElem_cons (by omega), hz,
      show i-1+1=i by omega]
  have hsafe : ZeroSafe (0 :: Y.drop i) := by
    simpa [hR] using zeroSafe_drop hs (i-1)
  have hfloor : WFloor (Y.drop i) := by
    have hd : (Y.drop r).drop (i-r) = Y.drop i := by
      rw [List.drop_drop, show r + (i-r) = i by omega]
    rw [← hd]
    exact WFloor_drop (Y.drop r) hf (i-r) (by simp [List.length_drop]; omega)
  have h := score_lt_first_W_stable (Y.drop i) hsafe hfloor m
  have hsi := suf_W_run_after_Y Y i m hiY
  have hti : suf (Y ++ tW) (i+1) = Y.drop i ++ tW := by
    simpa [copies] using suf_W_run_after_Y Y i 0 hiY
  have hfm : suf (Y ++ copies tW (m+1)) (Y.length+2) =
      [1,2,1] ++ copies tW m := by
    have h0 := suf_app Y (copies tW (m+1)) 1
    rw [copies_succ] at h0
    rw [copies_succ]
    simpa [tW] using h0
  have hf0 : suf (Y ++ tW) (Y.length+2) = [1,2,1] := by
    simpa [tW] using suf_app Y tW 1
  rw [hsi, hti, hfm, hf0]
  exact h

theorem score_le_W_run_stable (Y : List ℕ) (hs : ZeroSafe Y)
    (r i j m : ℕ) (hf : WFloor (Y.drop r))
    (hri : r ≤ i) (hrj : r ≤ j)
    (hiY : i ≤ Y.length) (hjY : j ≤ Y.length) :
    (suf (Y ++ copies tW (m+1)) (i+1) ≤
      suf (Y ++ copies tW (m+1)) (j+1)) ↔
      (suf (Y ++ tW) (i+1) ≤ suf (Y ++ tW) (j+1)) := by
  let S := Y ++ copies tW (m+1)
  let T := Y ++ tW
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hlt := score_lt_W_run_stable Y hs r i j m hf hri hij hjY
    have hneS : suf S (i+1) ≠ suf S (j+1) := by
      intro he
      have h := suf_succ_inj S i j (by simp [S]; omega) (by simp [S]; omega) he
      omega
    have hneT : suf T (i+1) ≠ suf T (j+1) := by
      intro he
      have h := suf_succ_inj T i j (by simp [T]; omega) (by simp [T]; omega) he
      omega
    constructor
    · intro hle
      exact ((hlt).mp (lt_of_le_of_ne hle hneS)).le
    · intro hle
      exact ((hlt).mpr (lt_of_le_of_ne hle hneT)).le
  · simp
  · have hlt := score_lt_W_run_stable Y hs r j i m hf hrj hji hiY
    constructor
    · intro hle
      apply le_of_not_gt
      intro hgt
      exact (not_le_of_gt (hlt.mpr hgt) hle).elim
    · intro hle
      apply le_of_not_gt
      intro hgt
      exact (not_le_of_gt (hlt.mp hgt) hle).elim

theorem score_le_first_W_at_Y (Y : List ℕ) (hs : ZeroSafe Y)
    (r i m : ℕ) (hf : WFloor (Y.drop r)) (hri : r ≤ i)
    (hi : 1 ≤ i) (hiY : i ≤ Y.length) (hz : Y[i-1] = 0) :
    (suf (Y ++ copies tW (m+1)) (i+1) ≤
      suf (Y ++ copies tW (m+1)) (Y.length+2)) ↔
      (suf (Y ++ tW) (i+1) ≤ suf (Y ++ tW) (Y.length+2)) := by
  have hlt := score_lt_first_W_at_Y Y hs r i m hf hri hi hiY hz
  let S := Y ++ copies tW (m+1)
  let T := Y ++ tW
  have hneS : suf S (i+1) ≠ suf S (Y.length+2) := by
    intro he
    have h := suf_succ_inj S i (Y.length+1)
      (by simp [S]; omega) (by simp [S, copies_length, tW]; omega) he
    omega
  have hneT : suf T (i+1) ≠ suf T (Y.length+2) := by
    intro he
    have h := suf_succ_inj T i (Y.length+1)
      (by simp [T, tW]; omega) (by simp [T, tW]) he
    omega
  constructor
  · intro hle
    exact (hlt.mp (lt_of_le_of_ne hle hneS)).le
  · intro hle
    exact (hlt.mpr (lt_of_le_of_ne hle hneT)).le

theorem candidate_W_run_prefix_iff (Y : List ℕ) (i m : ℕ)
    (hi : 1 ≤ i) (hiY : i ≤ Y.length) :
    Candidate (Y ++ copies tW (m+1)) i ↔ Candidate (Y ++ tW) i := by
  have hm : entry (Y ++ copies tW (m+1))
      (Y ++ copies tW (m+1)).length = 1 := by
    exact entry_last _ (Y ++ copies tW m ++ [0,1,2]) 1
      (by simp [copies_succ', tW, List.append_assoc])
  have h0 : entry (Y ++ tW) (Y ++ tW).length = 1 := by
    exact entry_last _ (Y ++ [0,1,2]) 1 (by simp [tW])
  have him : entry (Y ++ copies tW (m+1)) i = Y[i-1] := by
    simp only [entry]
    rw [List.getElem?_append_left (l₁ := Y) (l₂ := copies tW (m+1))
      (i := i-1) (by omega), List.getElem?_eq_getElem (by omega)]
    rfl
  have hi0 : entry (Y ++ tW) i = Y[i-1] := by
    simp only [entry]
    rw [List.getElem?_append_left (l₁ := Y) (l₂ := tW)
      (i := i-1) (by omega), List.getElem?_eq_getElem (by omega)]
    rfl
  simp only [Candidate, hm, h0, him, hi0]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨by simp [tW]; omega, h⟩
  · rintro ⟨_, h⟩
    exact ⟨by simp [copies_length, tW]; omega, h⟩

theorem tailsLe_W_run_all (m : ℕ) :
    TailsLe 1 ([1,2,1] ++ copies tW m) (copies tW (m+1)) [] := by
  rw [copies_succ, tailsLe_append]
  refine ⟨?_, ?_⟩
  · simp only [tW, TailsLe, List.cons_append, List.nil_append]
    exact ⟨fun _ => by simp, by omega, by omega, by omega, trivial⟩
  · simpa using tailsLe_copies_W_run m 0

theorem score_W_run_le_first (Y : List ℕ) (m j : ℕ)
    (hj0 : Y.length + 1 ≤ j)
    (hjL : j < (Y ++ copies tW (m+1)).length)
    (hj : Candidate (Y ++ copies tW (m+1)) j) :
    suf (Y ++ copies tW (m+1)) (j+1) ≤
      suf (Y ++ copies tW (m+1)) (Y.length+2) := by
  let A := copies tW (m+1)
  let k := j - Y.length - 1
  have hk : k < A.length := by simp [A, k] at hjL ⊢; omega
  have hjk : j = Y.length + k + 1 := by simp [k]; omega
  have he : A[k] < 1 := by
    have he0 : entry (Y ++ A) j = A[k] := by
      rw [hjk]
      exact entry_app Y A k hk
    have hlast : entry (Y ++ A) (Y ++ A).length = 1 :=
      entry_last _ (Y ++ copies tW m ++ [0,1,2]) 1
        (by simp [A, copies_succ', tW, List.append_assoc])
    have hh := hj.2
    change entry (Y ++ A) j < entry (Y ++ A) (Y ++ A).length at hh
    rw [he0, hlast] at hh
    exact hh
  have hscore : suf (Y ++ A) (j+1) = A.drop (k+1) := by
    simpa [hjk, Nat.add_assoc] using suf_app Y A (k+1)
  have hfirst : suf (Y ++ A) (Y.length+2) = [1,2,1] ++ copies tW m := by
    have h0 := suf_app Y A 1
    change suf (Y ++ copies tW (m+1)) (Y.length+2) = _
    rw [copies_succ]
    rw [show A = tW ++ copies tW m by simp [A, copies_succ]] at h0
    simpa [tW] using h0
  rw [hscore, hfirst]
  change A.drop (k+1) ≤ [1,2,1] ++ copies tW m
  simpa only [List.append_nil] using
    (tailsLe_spec 1 ([1,2,1] ++ copies tW m) A []).mp
      (by simpa [A] using tailsLe_W_run_all m) k hk he

theorem candidate_W_single_tail (Y : List ℕ) (j : ℕ)
    (hj : Y.length + 1 ≤ j) (hc : Candidate (Y ++ tW) j) :
    j = Y.length + 1 := by
  let k := j - Y.length - 1
  have hjk : j = Y.length + k + 1 := by simp [k]; omega
  have hk : k < 3 := by
    have := hc.1
    simp [tW] at this
    omega
  have hk4 : k < tW.length := by simp [tW]; omega
  have hlast : entry (Y ++ tW) (Y ++ tW).length = 1 :=
    entry_last _ (Y ++ [0,1,2]) 1 (by simp [tW])
  have he : entry (Y ++ tW) j = tW[k] := by
    rw [hjk]
    exact entry_app Y tW k hk4
  have hlt := hc.2
  rw [he, hlast] at hlt
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hkcases with h | h | h
  · rw [h] at hjk
    simpa using hjk
  · simp [h, tW] at hlt
  · simp [h, tW] at hlt

theorem candidate_first_W (Y : List ℕ) (m : ℕ) :
    Candidate (Y ++ copies tW (m+1)) (Y.length+1) := by
  have he : entry (Y ++ copies tW (m+1)) (Y.length+1) = 0 := by
    rw [copies_succ]
    simpa [tW] using entry_at (Y ++ (tW ++ copies tW m)) Y
      (tW ++ copies tW m) 0 (Y.length+1) rfl rfl (by simp [tW])
  have hlast : entry (Y ++ copies tW (m+1))
      (Y ++ copies tW (m+1)).length = 1 :=
    entry_last _ (Y ++ copies tW m ++ [0,1,2]) 1
      (by simp [copies_succ', tW, List.append_assoc])
  exact ⟨by simp [copies_length,tW]; omega, by rw [he,hlast]; omega⟩

theorem candidate_prefix_zero (Y : List ℕ) (i : ℕ)
    (hi : 1 ≤ i) (hiY : i ≤ Y.length)
    (hc : Candidate (Y ++ tW) i) : Y[i-1] = 0 := by
  have he : entry (Y ++ tW) i = Y[i-1] := by
    simp only [entry]
    rw [List.getElem?_append_left (l₁ := Y) (l₂ := tW)
      (i := i-1) (by omega), List.getElem?_eq_getElem (by omega)]
    rfl
  have hlast : entry (Y ++ tW) (Y ++ tW).length = 1 :=
    entry_last _ (Y ++ [0,1,2]) 1 (by simp [tW])
  have h := hc.2
  rw [he, hlast] at h
  omega

theorem mbp_W_run_stable (Y : List ℕ) (hs : ZeroSafe Y) (hY : Y ≠ [])
    (m : ℕ) :
    let r := sp (Y ++ tW) (Y.length+1)
    mbp (Y ++ copies tW (m+1)) r = mbp (Y ++ tW) r := by
  intro r
  let T := Y ++ tW
  let S := Y ++ copies tW (m+1)
  let c := mbp T r
  let j0 := Y.length+1
  have hYL : 1 ≤ Y.length := List.length_pos_iff.mpr hY
  have hrle : r ≤ Y.length := by
    have h := sp_lt T (Y.length+1) (by omega)
    simpa [r, T] using h
  have hrlo : 1 ≤ r := one_le_sp T _
  have hf : WFloor (Y.drop r) := WFloor_after_sp_W Y r (by rfl) hrle
  have hj0 : Candidate T j0 := by
    simpa [T, j0, copies] using candidate_first_W Y 0
  have hrc : r ≤ c := by
    have h := (mbp_spec T r).1
    have hrT : r ≤ T.length := by simp [T, tW]; omega
    rw [min_eq_left hrT] at h
    dsimp [c]
    omega
  have hc : Candidate T c := mbp_candidate_of_exists T r j0 (by omega) hj0
  have hcYor : c ≤ Y.length ∨ c = j0 := by
    by_cases hcY : c ≤ Y.length
    · exact Or.inl hcY
    · exact Or.inr (candidate_W_single_tail Y c (by omega) hc)
  have hcS : Candidate S c := by
    rcases hcYor with hcY | hceq
    · exact (candidate_W_run_prefix_iff Y c m (by omega) hcY).mpr hc
    · rw [hceq]
      simpa [S, j0] using candidate_first_W Y m
  have hfirstT : suf T (j0+1) ≤ suf T (c+1) :=
    ((mbp_spec T r).2.2.2 j0 (by omega) hj0).1
  have hfirstS : suf S (j0+1) ≤ suf S (c+1) := by
    rcases hcYor with hcY | hceq
    · have hz := candidate_prefix_zero Y c (by omega) hcY hc
      have hcmp := score_lt_first_W_at_Y Y hs r c m hf hrc (by omega) hcY hz
      apply le_of_not_gt
      intro hlt
      have hlt0 := hcmp.mp hlt
      exact (not_lt_of_ge hfirstT hlt0).elim
    · rw [hceq]
  have hbest : ∀ j, r ≤ j → Candidate S j →
      suf S (j+1) ≤ suf S (c+1) := by
    intro j hrj hj
    by_cases hjY : j ≤ Y.length
    · have hjT : Candidate T j :=
        (candidate_W_run_prefix_iff Y j m (by omega) hjY).mp hj
      have hbest0 : suf T (j+1) ≤ suf T (c+1) :=
        ((mbp_spec T r).2.2.2 j hrj hjT).1
      rcases hcYor with hcY | hceq
      · exact (score_le_W_run_stable Y hs r j c m hf hrj hrc hjY hcY).mpr hbest0
      · rw [hceq] at hbest0 ⊢
        have hz := candidate_prefix_zero Y j (by omega) hjY hjT
        exact (score_le_first_W_at_Y Y hs r j m hf hrj (by omega) hjY hz).mpr hbest0
    · have hj0lo : j0 ≤ j := by omega
      exact (score_W_run_le_first Y m j hj0lo (by simpa [S] using hj.1) hj).trans hfirstS
  exact mbp_eq_of_argmax S r c hrc hcS hbest

theorem rawWord_replicate_W (m : ℕ) :
    PrefixTok.rawWord (List.replicate m .W) = copies tW m := by
  simp [PrefixTok.rawWord, PrefixTok.raw, copies]

theorem cut_W_run_token_A0 (v : List PrefixTok) (m : ℕ) :
    cut (tA 0 ++ PrefixTok.rawWord v ++ copies tW (m+1)) =
      cut (tA 0 ++ PrefixTok.rawWord v ++ tW) := by
  let Y := tA 0 ++ PrefixTok.rawWord v
  let S := Y ++ copies tW (m+1)
  let T := Y ++ tW
  have hYsafe : ZeroSafe Y := by
    exact zeroSafe_append (zeroSafe_token (.A 0)) (zeroSafe_rawWord v)
  have hYne : Y ≠ [] := by simp [Y, tA]
  have hSshape : S = tA 0 ++ PrefixTok.rawWord (v ++ List.replicate m .W) ++ tW := by
    simp [S, Y, rawWord_append, rawWord_replicate_W, copies_succ', List.append_assoc]
  have hbrS : br S = 2 := by
    apply br_eq_two_of_breakAt S (by simp [S, tW, copies_length]; omega)
    rw [hSshape]
    exact breakAt_two_final_W (v ++ List.replicate m .W)
  have hbrT : br T = 2 := by
    apply br_eq_two_of_breakAt T (by simp [T, tW, Y, tA])
    simpa [T, Y, List.append_assoc] using breakAt_two_final_W v
  have hpS1 : p S 1 = (Y ++ copies tW m).length+1 := by
    rw [show S = (Y ++ copies tW m) ++ tW by
      simp [S, copies_succ', List.append_assoc]]
    exact p_one_final_W _
  have hpT1 : p T 1 = Y.length+1 := p_one_final_W Y
  have hp2 : p S 2 = p T 2 := by
    rw [p_succ, hpS1, p_succ, hpT1]
    exact sp_W_run_stable Y hYsafe hYne m
  have hfbp : fbp S 2 = fbp T 2 := by
    rw [fbp, fbp, hp2, p_succ, hpT1]
    simpa [S, T] using mbp_W_run_stable Y hYsafe hYne m
  change cut S = cut T
  simp only [cut, hbrS, hbrT]
  exact hfbp

theorem cut_W_run_token_depth_core (d : ℕ) (v : List PrefixTok) (m : ℕ) :
    cut (tA d ++ PrefixTok.rawWord v ++ copies tW (m+1)) =
      cut (tA d ++ PrefixTok.rawWord v ++ tW) := by
  have h := cut_W_run_token_A0 (List.replicate d .D ++ v) m
  simp only [rawWord_append, rawWord_replicate_D, List.append_assoc] at h
  simp only [← List.append_assoc] at h
  rw [show tA 0 ++ copies [0,2] d = tA d by
    simpa using (tA_append_D_copies 0 d)] at h
  simpa only [List.append_assoc] using h

theorem cut_prefix_depth_W_run (Z : List ℕ) (d : ℕ)
    (t : PrefixTok) (w : List PrefixTok) (hfirst : t ≠ .D)
    (hmin : ∀ j, .A j ∈ t :: w → d ≤ j) (m : ℕ) :
    cut (Z ++ tA d ++ PrefixTok.rawWord (t :: w) ++ copies tW (m+1)) =
      Z.length + cut (tA d ++ PrefixTok.rawWord (t :: w) ++ copies tW (m+1)) := by
  have hmin' : ∀ j, .A j ∈ t :: (w ++ List.replicate (m+1) .W) → d ≤ j := by
    intro j hj
    have hj' : .A j ∈ t :: w := by
      simpa using hj
    exact hmin j hj'
  have hlast : (t :: (w ++ List.replicate (m+1) .W)).getLast? ≠ some (.A d) := by
    rw [show t :: (w ++ List.replicate (m+1) .W) =
      (t :: w) ++ List.replicate (m+1) .W by simp,
      List.getLast?_append_of_ne_nil _ (by simp)]
    rw [List.replicate_succ', List.getLast?_append_cons]
    simp
  have h := cut_prefix_depth_token_word Z d t
    (w ++ List.replicate (m+1) .W) hfirst hmin' hlast
  rw [show t :: (w ++ List.replicate (m+1) .W) =
    (t :: w) ++ List.replicate (m+1) .W by simp,
    rawWord_append, rawWord_replicate_W] at h
  simpa only [List.append_assoc] using h

theorem cut_W_run_token_depth (Z : List ℕ) (d : ℕ)
    (t : PrefixTok) (w : List PrefixTok) (hfirst : t ≠ .D)
    (hmin : ∀ j, .A j ∈ t :: w → d ≤ j) (m : ℕ) :
    cut (Z ++ tA d ++ PrefixTok.rawWord (t :: w) ++ copies tW (m+1)) =
      cut (Z ++ tA d ++ PrefixTok.rawWord (t :: w) ++ tW) := by
  have hm := cut_prefix_depth_W_run Z d t w hfirst hmin m
  have h0 := cut_prefix_depth_W_run Z d t w hfirst hmin 0
  have hc := cut_W_run_token_depth_core d (t :: w) m
  have h0' : cut (Z ++ tA d ++ PrefixTok.rawWord (t :: w) ++ tW) =
      Z.length + cut (tA d ++ PrefixTok.rawWord (t :: w) ++ tW) := by
    simpa [copies] using h0
  rw [hm, h0', hc]

/-- Once the cut is fixed, every expansion repeats the same cut suffix;
additional `W` tokens are inserted in that suffix before the final decrement. -/
theorem fs_W_run_block_of_cut (Y : List ℕ) (m n : ℕ)
    (hcut : cut (Y ++ copies tW (m+1)) = cut (Y ++ tW)) :
    let T := Y ++ tW
    let c := cut T
    fs (Y ++ copies tW (m+1)) n =
      T.take c ++ copies ((T.drop c ++ copies tW m).dropLast ++ [0]) n := by
  intro T c
  let S := Y ++ copies tW (m+1)
  have hS : S = T ++ copies tW m := by
    simp [S, T, copies_succ, List.append_assoc]
  have hc : c ≤ T.length := cut_le_length T
  have hgood : S.take c = T.take c := by
    rw [hS, List.take_append_of_le_length hc]
  have hdrop : S.drop c = T.drop c ++ copies tW m := by
    rw [hS, List.drop_append_of_le_length hc]
  have hlast : entry S S.length = 1 :=
    entry_last _ (Y ++ copies tW m ++ [0,1,2]) 1
      (by simp [S, copies_succ', tW, List.append_assoc])
  have hne : S.isEmpty = false := by simp [S, tW, copies_succ]
  have hbad : bad S = (T.drop c ++ copies tW m).dropLast ++ [0] := by
    simp only [bad, hlast, Nat.reduceSub, ← List.dropLast_drop_eq_drop_dropLast]
    rw [show cut S = c by simpa [S, T, c] using hcut, hdrop]
  have hcut' : cut S = c := by simpa [S, T, c] using hcut
  change fs S n = _
  simp [fs, hne, hlast, good, hcut', hgood, hbad, copies]

theorem fs_W_run_token_depth (Z : List ℕ) (d : ℕ)
    (t : PrefixTok) (w : List PrefixTok) (hfirst : t ≠ .D)
    (hmin : ∀ j, .A j ∈ t :: w → d ≤ j) (m n : ℕ) :
    let Y := Z ++ tA d ++ PrefixTok.rawWord (t :: w)
    let T := Y ++ tW
    let c := cut T
    fs (Y ++ copies tW (m+1)) n =
      T.take c ++ copies ((T.drop c ++ copies tW m).dropLast ++ [0]) n := by
  intro Y T c
  have hc : cut (Y ++ copies tW (m+1)) = cut (Y ++ tW) := by
    simpa [Y, List.append_assoc] using
      cut_W_run_token_depth Z d t w hfirst hmin m
  exact fs_W_run_block_of_cut Y m n hc

/-- A terminal `W D` keeps the external prefix, at any permitted depth. -/
theorem fs_W_D_token_prefix (Z : List ℕ) (d : ℕ)
    (t : PrefixTok) (w : List PrefixTok) (hfirst : t ≠ .D)
    (hmin : ∀ j, .A j ∈ t :: w → d ≤ j) (n : ℕ) :
    fs (Z ++ tA d ++ PrefixTok.rawWord (t :: w) ++ tW ++ [0,2]) n =
      Z ++ fs (tA d ++ PrefixTok.rawWord (t :: w) ++ tW ++ [0,2]) n := by
  have hmin' : ∀ j, .A j ∈ t :: (w ++ [.W, .D]) → d ≤ j := by
    intro j hj
    have hj' : .A j ∈ t :: w := by simpa using hj
    exact hmin j hj'
  have hlast : (t :: (w ++ [.W, .D])).getLast? ≠ some (.A d) := by
    rw [show t :: (w ++ [.W, .D]) = (t :: w) ++ [.W, .D] by simp,
      List.getLast?_append_of_ne_nil _ (by simp)]
    simp
  have h := fs_prefix_depth_token_word Z d t (w ++ [.W, .D])
    hfirst hmin' hlast n
  rw [show t :: (w ++ [.W, .D]) = (t :: w) ++ [.W, .D] by simp,
    rawWord_append] at h
  simpa [PrefixTok.rawWord, PrefixTok.raw, List.append_assoc] using h

theorem fs_W_D_of_cut (Y : List ℕ) (n : ℕ)
    (hc : cut (Y ++ tW ++ [0,2]) = Y.length+2) :
    fs (Y ++ tW ++ [0,2]) n = Y ++ copies tW n ++ [0,1] := by
  have hS : Y ++ tW ++ [0,2] = (Y ++ [0,1]) ++ [2,1,0] ++ [2] := by
    simp [tW, List.append_assoc]
  have hcut : cut (Y ++ tW ++ [0,2]) = (Y ++ [0,1]).length := by
    simpa using hc
  rw [fs_of_cut_word _ (Y ++ [0,1]) [2,1,0] 2 hS (by decide) hcut n]
  have hr := copies_rotate [2,1] [0,1] n
  simp only [List.append_assoc] at hr ⊢
  simpa [tW, List.append_assoc] using congrArg (fun r => Y ++ r) hr

theorem cut_W_W_D (X : List ℕ) :
    cut (X ++ tW ++ tW ++ [0,2]) = (X ++ tW).length+2 := by
  let S := X ++ tW ++ tW ++ [0,2]
  have hp2 : p S 2 = (X ++ tW).length+1 := by
    simpa [S, List.append_assoc, copies] using p_two_final_W_D_run (X ++ tW) 0
  have hp3 : p S 3 = X.length+1 := by
    rw [p_succ, hp2]
    refine sp_dec S X [1,2,1] (tW ++ [0,2]) 0 _ _
      (by simp [S, tW, List.append_assoc]) (by simp [tW]) rfl ?_ ?_
    · decide
    · simp only [GeAll, tW, List.cons_append, List.nil_append]
      exact ⟨cons_le_of_lt _ _ _ _ (by decide),
        cons_le_of_lt _ _ _ _ (by decide),
        cons_le_of_lt _ _ _ _ (by decide), trivial⟩
  have hh : entry S S.length = 2 :=
    entry_last S (X ++ tW ++ tW ++ [0]) 2 (by simp [S, List.append_assoc])
  have hm2 : mbp S ((X ++ tW).length+1) = (X ++ tW).length+2 := by
    refine mbp_dec S (X ++ tW) [0] [2,1,0,2] 1 2 _ _
      (by simp [S, tW, List.append_assoc]) rfl (by simp [tW])
      (by decide) hh (by decide)
      (by
        simp [TailsLe]
        exact ⟨cons_le_of_lt _ _ _ _ (by decide),
          cons_le_of_lt _ _ _ _ (by decide),
          cons_le_cons_same 2 [] [1,0,2] (nil_le_list _)⟩)
  have hm3 : mbp S (X.length+1) = (X ++ tW).length+2 := by
    refine mbp_dec S X (tW ++ [0]) [2,1,0,2] 1 2 _ _
      (by simp [S, tW, List.append_assoc]) rfl (by simp [tW])
      (by decide) hh (by decide)
      (by
        simp [TailsLe, tW]
        exact ⟨cons_le_of_lt _ _ _ _ (by decide),
          cons_le_cons_same 2 _ _
            (cons_le_cons_same 1 _ _
              (cons_le_cons_same 0 _ _ (cons_le_of_lt _ _ _ _ (by decide)))),
          cons_le_of_lt _ _ _ _ (by decide),
          cons_le_of_lt _ _ _ _ (by decide),
          cons_le_of_lt _ _ _ _ (by decide),
          cons_le_cons_same 2 [] [1,0,2] (nil_le_list _)⟩)
  have hf2 : fbp S 2 = (X ++ tW).length+2 := by
    simpa [fbp, hp2] using hm2
  have hf3 : fbp S 3 = (X ++ tW).length+2 := by
    simpa [fbp, hp3] using hm3
  have hb3 : breakAt S 3 := Or.inl (by rw [hf3, hf2])
  have hL : 3 ≤ S.length := by simp [S, tW]
  by_cases hb2 : breakAt S 2
  · have hbr : br S = 2 := br_eq_two_of_breakAt S (by omega) hb2
    change cut S = _
    simp only [cut, hbr]
    exact hf2
  · have hbr : br S = 3 := br_eq_three S hL hb2 hb3
    change cut S = _
    simp only [cut, hbr]
    exact hf3

theorem fs_W_W_D (X : List ℕ) (n : ℕ) :
    fs (X ++ tW ++ tW ++ [0,2]) n =
      X ++ tW ++ copies tW n ++ [0,1] := by
  simpa only [List.append_assoc] using fs_W_D_of_cut (X ++ tW) n (cut_W_W_D X)

theorem cut_E_W_D (X : List ℕ) :
    cut (X ++ tE ++ tW ++ [0,2]) = (X ++ tE).length+2 := by
  let S := X ++ tE ++ tW ++ [0,2]
  have hp2 : p S 2 = (X ++ tE).length+1 := by
    simpa [S, List.append_assoc, copies] using p_two_final_W_D_run (X ++ tE) 0
  have hp3 : p S 3 = X.length+1 := by
    rw [p_succ, hp2]
    refine sp_dec S X [1,2,0,2,1] (tW ++ [0,2]) 0 _ _
      (by simp [S, tE, tW, List.append_assoc]) (by simp [tE]) rfl ?_ ?_
    · decide
    · simp only [GeAll, tW, List.cons_append, List.nil_append]
      exact ⟨cons_le_of_lt _ _ _ _ (by decide),
        cons_le_of_lt _ _ _ _ (by decide),
        cons_le_cons_same 0 _ _ (cons_le_of_lt _ _ _ _ (by decide)),
        cons_le_of_lt _ _ _ _ (by decide),
        cons_le_of_lt _ _ _ _ (by decide), trivial⟩
  have hh : entry S S.length = 2 :=
    entry_last S (X ++ tE ++ tW ++ [0]) 2 (by simp [S, List.append_assoc])
  have hm2 : mbp S ((X ++ tE).length+1) = (X ++ tE).length+2 := by
    refine mbp_dec S (X ++ tE) [0] [2,1,0,2] 1 2 _ _
      (by simp [S, tW, List.append_assoc]) rfl (by simp [tE])
      (by decide) hh (by decide)
      (by
        simp [TailsLe]
        exact ⟨cons_le_of_lt _ _ _ _ (by decide),
          cons_le_of_lt _ _ _ _ (by decide),
          cons_le_cons_same 2 [] [1,0,2] (nil_le_list _)⟩)
  have hm3 : mbp S (X.length+1) = (X ++ tE).length+2 := by
    refine mbp_dec S X (tE ++ [0]) [2,1,0,2] 1 2 _ _
      (by simp [S, tE, tW, List.append_assoc]) rfl (by simp [tE])
      (by decide) hh (by decide)
      (by
        simp [TailsLe, tE]
        exact ⟨cons_le_of_lt _ _ _ _ (by decide),
          cons_le_cons_same 2 _ _ (cons_le_of_lt _ _ _ _ (by decide)),
          cons_le_cons_same 2 _ _
            (cons_le_cons_same 1 _ _
              (cons_le_cons_same 0 _ _ (cons_le_of_lt _ _ _ _ (by decide)))),
          cons_le_of_lt _ _ _ _ (by decide),
          cons_le_of_lt _ _ _ _ (by decide),
          cons_le_of_lt _ _ _ _ (by decide),
          cons_le_cons_same 2 [] [1,0,2] (nil_le_list _)⟩)
  have hf2 : fbp S 2 = (X ++ tE).length+2 := by simpa [fbp, hp2] using hm2
  have hf3 : fbp S 3 = (X ++ tE).length+2 := by simpa [fbp, hp3] using hm3
  have hb3 : breakAt S 3 := Or.inl (by rw [hf3, hf2])
  have hL : 3 ≤ S.length := by simp [S, tE, tW]
  by_cases hb2 : breakAt S 2
  · have hbr : br S = 2 := br_eq_two_of_breakAt S (by omega) hb2
    change cut S = _
    simp only [cut, hbr]
    exact hf2
  · have hbr : br S = 3 := br_eq_three S hL hb2 hb3
    change cut S = _
    simp only [cut, hbr]
    exact hf3

theorem fs_E_W_D (X : List ℕ) (n : ℕ) :
    fs (X ++ tE ++ tW ++ [0,2]) n =
      X ++ tE ++ copies tW n ++ [0,1] := by
  simpa only [List.append_assoc] using fs_W_D_of_cut (X ++ tE) n (cut_E_W_D X)

theorem cut_A_W_D (X : List ℕ) (k : ℕ) :
    cut (X ++ tA k ++ tW ++ [0,2]) = (X ++ tA k).length+2 := by
  let S := X ++ tA k ++ tW ++ [0,2]
  have hp2 : p S 2 = (X ++ tA k).length+1 := by
    simpa [S, List.append_assoc, copies] using p_two_final_W_D_run (X ++ tA k) 0
  have hp3 : p S 3 = X.length+1 := by
    rw [p_succ, hp2]
    refine sp_dec S X ([1,2] ++ copies [0,2] k) (tW ++ [0,2]) 0 _ _
      (by simp [S, tA, List.append_assoc]) (by simp [tA]; omega) rfl ?_ ?_
    · cases k with
      | zero => simp [copies, tW, List.cons_lt_cons_iff]
      | succ k =>
          rw [copies_succ]
          simp [tW, List.cons_lt_cons_iff]
    · rw [geAll_append]
      constructor
      · simp only [GeAll, List.cons_append, List.nil_append]
        exact ⟨cons_le_of_lt _ _ _ _ (by decide),
          cons_le_of_lt _ _ _ _ (by decide), trivial⟩
      · change GeAll (0 :: 1 :: [2,1,0,2]) (copies [0,2] k) (tW ++ [0,2])
        exact geAll_copies_02_gen [2,1,0,2] k (tW ++ [0,2])
  have hh : entry S S.length = 2 :=
    entry_last S (X ++ tA k ++ tW ++ [0]) 2 (by simp [S, List.append_assoc])
  have hWD : TailsLe 2 [2,1,0,2] (tW ++ [0,2]) [] := by
    simp [TailsLe, tW]
    exact ⟨cons_le_of_lt _ _ _ _ (by decide),
      cons_le_of_lt _ _ _ _ (by decide),
      cons_le_cons_same 2 [] [1,0,2] (nil_le_list _)⟩
  have hm2 : mbp S ((X ++ tA k).length+1) = (X ++ tA k).length+2 := by
    refine mbp_dec S (X ++ tA k) [0] [2,1,0,2] 1 2 _ _
      (by simp [S, tW, List.append_assoc]) rfl (by simp [tA])
      (by decide) hh (by decide) (by simpa [tW] using hWD)
  have hm3 : mbp S (X.length+1) = (X ++ tA k).length+2 := by
    have hD : TailsLe 2 [2,1,0,2] (copies [0,2] k) (tW ++ [0,2]) := by
      simpa [tW] using tailsLe_copies_02_mid [0,2] k [1,2,1,0,2]
    have hRest : TailsLe 2 [2,1,0,2]
        (copies [0,2] k ++ (tW ++ [0,2])) [] :=
      (tailsLe_append _ _ _ _ _).mpr ⟨by simpa using hD, hWD⟩
    have hHead : TailsLe 2 [2,1,0,2] [0,1,2]
        (copies [0,2] k ++ (tW ++ [0,2])) := by
      simp only [TailsLe, List.cons_append, List.nil_append]
      refine ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide), ?_, by omega, trivial⟩
      intro _
      obtain ⟨V, hV⟩ := copies_02_head k [1,2,1,0,2]
      change copies [0,2] k ++ (0 :: [1,2,1,0,2]) = 0 :: V at hV
      change 2 :: (copies [0,2] k ++ [0,1,2,1,0,2]) ≤ [2,1,0,2]
      rw [hV]
      exact cons_le_cons_same 2 _ _ (cons_le_of_lt _ _ _ _ (by decide))
    have hAll : TailsLe 2 [2,1,0,2]
        ([0,1,2] ++ (copies [0,2] k ++ (tW ++ [0,2]))) [] :=
      (tailsLe_append _ _ _ _ _).mpr ⟨by simpa using hHead, hRest⟩
    refine mbp_dec S X (tA k ++ [0]) [2,1,0,2] 1 2 _ _
      (by simp [S, tA, tW, List.append_assoc]) rfl (by simp [tA]; omega)
      (by decide) hh (by decide)
      (by simpa [tA, tW, List.append_assoc] using hAll)
  have hf2 : fbp S 2 = (X ++ tA k).length+2 := by simpa [fbp, hp2] using hm2
  have hf3 : fbp S 3 = (X ++ tA k).length+2 := by simpa [fbp, hp3] using hm3
  have hb3 : breakAt S 3 := Or.inl (by rw [hf3, hf2])
  have hL : 3 ≤ S.length := by simp [S, tA, tW]; omega
  by_cases hb2 : breakAt S 2
  · have hbr : br S = 2 := br_eq_two_of_breakAt S (by omega) hb2
    change cut S = _
    simp only [cut, hbr]
    exact hf2
  · have hbr : br S = 3 := br_eq_three S hL hb2 hb3
    change cut S = _
    simp only [cut, hbr]
    exact hf3

theorem fs_A_W_D (X : List ℕ) (k n : ℕ) :
    fs (X ++ tA k ++ tW ++ [0,2]) n =
      X ++ tA k ++ copies tW n ++ [0,1] := by
  simpa only [List.append_assoc] using fs_W_D_of_cut (X ++ tA k) n (cut_A_W_D X k)

/-- A final `W D` repeats `W` when the token before that `W` is not `D`.
The empty preceding word uses the base `A_d` as that token. -/
theorem fs_W_D_after_token_word (Z : List ℕ) (d : ℕ)
    (v : List PrefixTok) (n : ℕ)
    (hlast : v = [] ∨ ∃ u t, v = u ++ [t] ∧ t ≠ .D) :
    fs (Z ++ tA d ++ PrefixTok.rawWord v ++ tW ++ [0,2]) n =
      Z ++ tA d ++ PrefixTok.rawWord v ++ copies tW n ++ [0,1] := by
  rcases hlast with hv | ⟨u, t, hv, ht⟩
  · subst v
    simpa [PrefixTok.rawWord, List.append_assoc] using fs_A_W_D Z d n
  · subst v
    cases t with
    | D => exact False.elim (ht rfl)
    | A k =>
        simpa [rawWord_append, rawWord_singleton, PrefixTok.raw,
          List.append_assoc] using fs_A_W_D (Z ++ tA d ++ PrefixTok.rawWord u) k n
    | E =>
        simpa [rawWord_append, rawWord_singleton, PrefixTok.raw,
          List.append_assoc] using fs_E_W_D (Z ++ tA d ++ PrefixTok.rawWord u) n
    | W =>
        simpa [rawWord_append, rawWord_singleton, PrefixTok.raw,
          List.append_assoc] using fs_W_W_D (Z ++ tA d ++ PrefixTok.rawWord u) n

def tWWD : List ℕ := tW ++ tW ++ [0,2]

theorem cut_WDW_run_W_D (X : List ℕ) (m : ℕ) :
    cut (X ++ tA 0 ++ copies tWDW m ++ tW ++ [0,2]) =
      (X ++ tA 0 ++ copies tWDW m).length+2 := by
  cases m with
  | zero => simpa [copies, List.append_assoc] using cut_A_W_D X 0
  | succ m =>
      have h := cut_W_W_D (X ++ tA 0 ++ copies tWDW m ++ tW ++ [0,2])
      simpa [copies_succ', tWDW, List.append_assoc] using h

theorem fs_WDW_run_W_D (X : List ℕ) (m n : ℕ) :
    fs (X ++ tA 0 ++ copies tWDW m ++ tW ++ [0,2]) n =
      X ++ tA 0 ++ copies tWDW m ++ copies tW n ++ [0,1] := by
  simpa only [List.append_assoc] using
    fs_W_D_of_cut (X ++ tA 0 ++ copies tWDW m) n (cut_WDW_run_W_D X m)

theorem cut_WWD_run_W_W_D (X : List ℕ) (m : ℕ) :
    cut (X ++ tA 0 ++ copies tWWD m ++ tW ++ tW ++ [0,2]) =
      (X ++ tA 0 ++ copies tWWD m ++ tW).length+2 := by
  simpa only [List.append_assoc] using cut_W_W_D (X ++ tA 0 ++ copies tWWD m)

theorem fs_WWD_run_W_W_D (X : List ℕ) (m n : ℕ) :
    fs (X ++ tA 0 ++ copies tWWD m ++ tW ++ tW ++ [0,2]) n =
      X ++ tA 0 ++ copies tWWD m ++ tW ++ copies tW n ++ [0,1] := by
  simpa only [List.append_assoc] using
    fs_W_D_of_cut (X ++ tA 0 ++ copies tWWD m ++ tW) n
      (cut_WWD_run_W_W_D X m)

/-- The tokens before the last `W` of a nonempty `WDW` run. -/
def wdwPreWord : ℕ → List PrefixTok
  | 0 => [.W, .D]
  | m+1 => [.W, .D, .W] ++ wdwPreWord m

theorem raw_wdwPreWord (m : ℕ) :
    PrefixTok.rawWord (wdwPreWord m) = copies tWDW m ++ tW ++ [0,2] := by
  induction m with
  | zero => simp [wdwPreWord, PrefixTok.rawWord, PrefixTok.raw, copies]
  | succ m ih =>
      rw [wdwPreWord, rawWord_append, ih, copies_succ]
      simp [PrefixTok.rawWord, PrefixTok.raw, tWDW, List.append_assoc]

theorem cut_WDW_run_self (X : List ℕ) (m : ℕ) :
    cut (X ++ tA 0 ++ copies tWDW (m+1)) = X.length + 8 := by
  obtain ⟨v, hv⟩ : ∃ v, wdwPreWord m = .W :: v := by
    cases m with
    | zero => exact ⟨[.D], rfl⟩
    | succ m => exact ⟨[.D,.W] ++ wdwPreWord m, rfl⟩
  have hc := cut_W_run_token_depth X 0 .W v (by decide)
    (by intro j _; omega) 1
  have hraw := raw_wdwPreWord m
  rw [hv] at hraw
  rw [hraw] at hc
  have htwo : copies tW (1+1) = tW ++ tW := by simp [copies]
  rw [htwo] at hc
  have h : cut (X ++ tA 0 ++ copies tWDW (m+1) ++ tW) =
      cut (X ++ tA 0 ++ copies tWDW (m+1)) := by
    simpa [copies_succ', tWDW, List.append_assoc] using hc
  exact h.symm.trans (cut_WDW_run X m)

end SSOS.Seq
