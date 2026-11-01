import SSOS.WRunCut

/-!
# The cut of a last `V` and a last `L_k` (§43 of the 2026-10-17 notes)

Tokens after `P = (0,0,2,1,0,2)`: `V = (0,2,1)`, `D = (0,2)`, `Z = (0)`, `L_k = (0,1^k)`.

The core lemma `cut_last_one_core` treats every last unit `0⌢M'⌢1` whose middle `M'` has no
zero. Its first parent `p 1` is the head `0` of that unit after every prefix. Its second parent
`p 2` is the head `c` of a lower unit `c⌢A`; if no zero of `c⌢A` is followed by a tail above
`M'⌢1`, the record stays at the head of the last unit, `br = 2`, and the cut is right after
that head.

* `fs_V_core`, `fs_V_token`: `X⌢V [n] = X⌢D^n⌢0` (the V law) when the last token of `X` is
  `Z`, `L_j`, `D`, `A_k` or `W`, after every prefix.
* `fs_L_core`, `fs_L_after_L`: `X⌢L_(j+1) [n] = X⌢0⌢(1^j⌢0)^n` when the last token of `X`
  is `Z` or `L_i` with `i ≤ j`, after every prefix.
-/

namespace SSOS.Seq

def tV : List ℕ := [0,2,1]

/-- A list without small entries has no tail below the bound `h`. -/
theorem tailsLe_of_ge (h : ℕ) (M L B : List ℕ) (hL : ∀ x ∈ L, h ≤ x) : TailsLe h M L B := by
  induction L with
  | nil => simp [TailsLe]
  | cons x L ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    exact ⟨fun hx => absurd hL.1 (by omega), ih hL.2⟩

/-- Every suffix of `M'⌢1` is at least `(1)` when `M'` has no zero. -/
theorem geAll_one_of_pos (M' : List ℕ) (hM : ∀ x ∈ M', 1 ≤ x) : GeAll [1] M' [1] := by
  induction M' with
  | nil => simp [GeAll]
  | cons x M' ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hM
    refine ⟨?_, ih hM.2⟩
    rcases Nat.lt_or_ge 1 x with h | h
    · exact cons_le_of_lt _ _ _ _ h
    · obtain rfl : x = 1 := by omega
      exact cons_le_cons_same 1 _ _ (nil_le_list _)

/-- Core: last unit `0⌢M'⌢1` (no zero in `M'`) after a lower unit `c⌢A` that holds the
second parent. -/
theorem cut_last_one_core (Y A M' : List ℕ) (c : ℕ) (hM : ∀ x ∈ M', 1 ≤ x)
    (hlt : c :: (A ++ 0 :: (M' ++ [1])) < 0 :: (M' ++ [1]))
    (hgap : GeAll (0 :: (M' ++ [1])) A (0 :: (M' ++ [1])))
    (hT : TailsLe 1 (M' ++ [1]) (c :: A) (0 :: (M' ++ [1]))) :
    let S := Y ++ c :: A ++ 0 :: (M' ++ [1])
    p S 1 = Y.length + A.length + 2 ∧ p S 2 = Y.length + 1 ∧ br S = 2 ∧
      cut S = Y.length + A.length + 2 := by
  intro S
  have hL : S.length = Y.length + A.length + M'.length + 3 := by simp [S]; omega
  have hh : entry S S.length = 1 :=
    entry_last S (Y ++ c :: A ++ 0 :: M') 1 (by simp [S])
  have hp1 : p S 1 = Y.length + A.length + 2 := by
    rw [p_one_eq_sp, hL]
    exact sp_dec S (Y ++ c :: A) M' [1] 0 _ _ (by simp [S]) (by simp; omega) (by simp; omega)
      (cons_lt_of_lt _ _ _ _ (by decide)) (geAll_one_of_pos M' hM)
  have hp2 : p S 2 = Y.length + 1 := by
    rw [p_succ, hp1]
    exact sp_dec S Y A (0 :: (M' ++ [1])) c _ _ (by simp [S]) (by simp) rfl hlt hgap
  have hMne : M' ++ [1] ≠ [] := by simp
  have hm1 : mbp S (Y.length + A.length + 2) = Y.length + A.length + 2 := by
    refine mbp_dec S (Y ++ c :: A) [] (M' ++ [1]) 0 1 _ _ (by simp [S]) (by simp; omega)
      (by simp; omega) hMne hh (by decide) ?_
    simp only [List.nil_append, TailsLe]
    refine ⟨fun _ => by simp, tailsLe_of_ge _ _ _ _ ?_⟩
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hM x hx
    · exact le_rfl
  have hm2 : mbp S (Y.length + 1) = Y.length + A.length + 2 := by
    refine mbp_dec S Y (c :: A) (M' ++ [1]) 0 1 _ _ (by simp [S]) rfl (by simp; omega) hMne hh
      (by decide) ?_
    rw [tailsLe_append]
    refine ⟨by rw [List.append_nil]; exact hT, ?_⟩
    simp only [TailsLe]
    refine ⟨fun _ => by simp, tailsLe_of_ge _ _ _ _ ?_⟩
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hM x hx
    · exact le_rfl
  have hf1 : fbp S 1 = Y.length + A.length + 2 := by simp only [fbp, hp1, hm1]
  have hf2 : fbp S 2 = Y.length + A.length + 2 := by simp only [fbp, hp2, hm2]
  have hbr : br S = 2 := br_eq_two_of_breakAt S (by omega)
    (breakAt_two_of_eq S (by rw [hf1, hf2]))
  exact ⟨hp1, hp2, hbr, by rw [cut, hbr, hf2]⟩

/-- The expansion of the core: the copy starts right after the head `0` of the last unit. -/
theorem fs_last_one_core (Y A M' : List ℕ) (c : ℕ) (hM : ∀ x ∈ M', 1 ≤ x)
    (hlt : c :: (A ++ 0 :: (M' ++ [1])) < 0 :: (M' ++ [1]))
    (hgap : GeAll (0 :: (M' ++ [1])) A (0 :: (M' ++ [1])))
    (hT : TailsLe 1 (M' ++ [1]) (c :: A) (0 :: (M' ++ [1]))) (n : ℕ) :
    fs (Y ++ c :: A ++ 0 :: (M' ++ [1])) n = Y ++ c :: A ++ [0] ++ copies (M' ++ [0]) n := by
  have hc := (cut_last_one_core Y A M' c hM hlt hgap hT).2.2.2
  have h := fs_of_cut_word (Y ++ c :: A ++ 0 :: (M' ++ [1])) (Y ++ c :: A ++ [0]) M' 1
    (by simp) (by decide) (by rw [hc]; simp; omega) n
  simpa using h

/-! ## Last token `V` -/

/-- The V law in its general form: `X = Y⌢c⌢A`, `c` is the second parent (`hlt`, `hgap`) and
no zero of `c⌢A` is followed by a tail above `(2,1)` (`hT`). Then `cut(X⌢V) = |X|+1`. -/
theorem cut_V_core (Y A : List ℕ) (c : ℕ) (hlt : c :: (A ++ tV) < tV) (hgap : GeAll tV A tV)
    (hT : TailsLe 1 [2,1] (c :: A) tV) :
    let S := Y ++ c :: A ++ tV
    p S 1 = Y.length + A.length + 2 ∧ p S 2 = Y.length + 1 ∧ br S = 2 ∧
      cut S = Y.length + A.length + 2 :=
  cut_last_one_core Y A [2] c (by simp) hlt hgap hT

theorem fs_V_core (Y A : List ℕ) (c : ℕ) (hlt : c :: (A ++ tV) < tV) (hgap : GeAll tV A tV)
    (hT : TailsLe 1 [2,1] (c :: A) tV) (n : ℕ) :
    fs (Y ++ c :: A ++ tV) n = Y ++ c :: A ++ copies [0,2] n ++ [0] := by
  have h := fs_last_one_core Y A [2] c (by simp) hlt hgap hT n
  simp only [tV, List.cons_append, List.nil_append] at h ⊢
  rw [h]
  have hrot := copies_rotate [2] [0] n
  simp only [List.cons_append, List.nil_append] at hrot
  simp only [List.append_assoc, List.cons_append, List.nil_append, hrot]

theorem tailsLe_ones (h : ℕ) (M : List ℕ) (k : ℕ) (B : List ℕ) (hh : h ≤ 1) :
    TailsLe h M (copies [1] k) B :=
  tailsLe_of_ge h M _ B (fun x hx => by
    simp only [copies, List.mem_flatten, List.mem_replicate] at hx
    obtain ⟨l, ⟨_, rfl⟩, hx⟩ := hx
    simp at hx; omega)

theorem geAll_ones (k : ℕ) (B : List ℕ) (hB : ∃ B', B = 0 :: B') :
    GeAll B (copies [1] k) B := by
  obtain ⟨B', rfl⟩ := hB
  induction k with
  | zero => simp [copies, GeAll]
  | succ k ih =>
    rw [copies_succ, geAll_append]
    exact ⟨⟨cons_le_of_lt _ _ _ _ (by decide), trivial⟩, ih⟩

/-- V after `L_k` (`k = 0` is `Z`), after every prefix `Y`. -/
theorem fs_V_after_L (Y : List ℕ) (k n : ℕ) :
    fs (Y ++ 0 :: copies [1] k ++ tV) n = Y ++ 0 :: copies [1] k ++ copies [0,2] n ++ [0] := by
  refine fs_V_core Y (copies [1] k) 0 ?_ (geAll_ones k tV ⟨[2,1], rfl⟩) ?_ n
  · cases k with
    | zero => simp [copies, tV]; decide
    | succ k =>
      rw [copies_succ]
      exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)
  · refine ⟨fun _ => ?_, tailsLe_ones _ _ _ _ le_rfl⟩
    cases k with
    | zero => simp [copies, tV]; exact cons_le_of_lt _ _ _ _ (by decide)
    | succ k => rw [copies_succ]; exact cons_le_of_lt _ _ _ _ (by decide)

/-- V after `Z = (0)`, after every prefix `Y`. -/
theorem fs_V_after_Z (Y : List ℕ) (n : ℕ) :
    fs (Y ++ [0] ++ tV) n = Y ++ [0] ++ copies [0,2] n ++ [0] := by
  simpa [copies] using fs_V_after_L Y 0 n

/-- V after `D = (0,2)`, after every prefix `Y`. -/
theorem fs_V_after_D (Y : List ℕ) (n : ℕ) :
    fs (Y ++ [0,2] ++ tV) n = Y ++ [0,2] ++ copies [0,2] n ++ [0] :=
  fs_V_core Y [2] 0 (by decide) (by simp only [tV, GeAll]; decide)
    (by simp only [tV, TailsLe]; decide) n

/-- V after `W = (0,1,2,1)`, after every prefix `Y`. -/
theorem fs_V_after_W (Y : List ℕ) (n : ℕ) :
    fs (Y ++ tW ++ tV) n = Y ++ tW ++ copies [0,2] n ++ [0] :=
  fs_V_core Y [1,2,1] 0 (by decide) (by simp only [tV, GeAll]; decide)
    (by simp only [tV, TailsLe]; decide) n

/-- V after `A_k = (0,1,2)⌢(0,2)^k`, after every prefix `Y`. -/
theorem fs_V_after_A (Y : List ℕ) (k n : ℕ) :
    fs (Y ++ tA k ++ tV) n = Y ++ tA k ++ copies [0,2] n ++ [0] := by
  cases k with
  | zero =>
    simpa [tA, copies] using
      fs_V_core Y [1,2] 0 (by decide) (by simp only [tV, GeAll]; decide)
        (by simp only [tV, TailsLe]; decide) n
  | succ k =>
    have h := fs_V_after_D (Y ++ tA k) n
    have hA : tA (k+1) = tA k ++ [0,2] := by simp [tA, copies_succ']
    rw [hA]
    simpa using h

/-- The V law for every last token `t ∈ {Z, L_k, D, A_k, W}` before `V`, after every prefix:
`Y⌢t⌢V [n] = Y⌢t⌢D^n⌢0`. -/
theorem fs_V_token (Y t : List ℕ) (n : ℕ)
    (ht : (∃ k, t = 0 :: copies [1] k) ∨ t = [0,2] ∨ (∃ k, t = tA k) ∨ t = tW) :
    fs (Y ++ t ++ tV) n = Y ++ t ++ copies [0,2] n ++ [0] := by
  rcases ht with ⟨k, rfl⟩ | rfl | ⟨k, rfl⟩ | rfl
  · exact fs_V_after_L Y k n
  · exact fs_V_after_D Y n
  · exact fs_V_after_A Y k n
  · exact fs_V_after_W Y n

theorem cut_V_token (Y t : List ℕ)
    (ht : (∃ k, t = 0 :: copies [1] k) ∨ t = [0,2] ∨ (∃ k, t = tA k) ∨ t = tW) :
    cut (Y ++ t ++ tV) = Y.length + t.length + 1 := by
  rcases ht with ⟨k, rfl⟩ | rfl | ⟨k, rfl⟩ | rfl
  · refine (cut_V_core Y (copies [1] k) 0 ?_ (geAll_ones k tV ⟨[2,1], rfl⟩) ?_).2.2.2.trans
      (by simp; omega)
    · cases k with
      | zero => simp [copies, tV]; decide
      | succ k =>
        rw [copies_succ]
        exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)
    · refine ⟨fun _ => ?_, tailsLe_ones _ _ _ _ le_rfl⟩
      cases k with
      | zero => simp [copies, tV]; exact cons_le_of_lt _ _ _ _ (by decide)
      | succ k => rw [copies_succ]; exact cons_le_of_lt _ _ _ _ (by decide)
  · exact (cut_V_core Y [2] 0 (by decide) (by simp only [tV, GeAll]; decide)
      (by simp only [tV, TailsLe]; decide)).2.2.2.trans (by simp)
  · cases k with
    | zero =>
      have h := (cut_V_core Y [1,2] 0 (by decide) (by simp only [tV, GeAll]; decide)
        (by simp only [tV, TailsLe]; decide)).2.2.2
      simp only [tA, copies, List.replicate_zero, List.flatten_nil, List.append_nil]
      simpa using h
    | succ k =>
      have h := (cut_V_core (Y ++ tA k) [2] 0 (by decide) (by simp only [tV, GeAll]; decide)
        (by simp only [tV, TailsLe]; decide)).2.2.2
      have hA : tA (k+1) = tA k ++ [0,2] := by simp [tA, copies_succ']
      rw [hA]
      simp at h ⊢
      omega
  · exact (cut_V_core Y [1,2,1] 0 (by decide) (by simp only [tV, GeAll]; decide)
      (by simp only [tV, TailsLe]; decide)).2.2.2.trans (by simp [tW])

/-! ## Last token `L_(j+1)` when its own head is chosen -/

/-- The L law in its general form: last unit `L_(j+1) = 0⌢1^(j+1)`. -/
theorem fs_L_core (Y A : List ℕ) (c j : ℕ)
    (hlt : c :: (A ++ 0 :: copies [1] (j+1)) < 0 :: copies [1] (j+1))
    (hgap : GeAll (0 :: copies [1] (j+1)) A (0 :: copies [1] (j+1)))
    (hT : TailsLe 1 (copies [1] (j+1)) (c :: A) (0 :: copies [1] (j+1))) (n : ℕ) :
    cut (Y ++ c :: A ++ 0 :: copies [1] (j+1)) = Y.length + A.length + 2 ∧
    fs (Y ++ c :: A ++ 0 :: copies [1] (j+1)) n =
      Y ++ c :: A ++ [0] ++ copies (copies [1] j ++ [0]) n := by
  have hM : ∀ x ∈ copies [1] j, 1 ≤ x := fun x hx => by
    simp only [copies, List.mem_flatten, List.mem_replicate] at hx
    obtain ⟨l, ⟨_, rfl⟩, hx⟩ := hx
    simp at hx; omega
  rw [copies_succ'] at hlt hgap hT ⊢
  exact ⟨(cut_last_one_core Y A (copies [1] j) c hM hlt hgap hT).2.2.2,
    fs_last_one_core Y A (copies [1] j) c hM hlt hgap hT n⟩

/-- `1^i⌢0⌢R` is below `1^(i+1+d)`. -/
theorem ones_zero_lt (i d : ℕ) (R : List ℕ) :
    copies [1] i ++ 0 :: R < copies [1] (i + 1 + d) := by
  induction i with
  | zero =>
    rw [show 0 + 1 + d = d + 1 by omega, copies_succ]
    simpa [copies] using cons_lt_of_lt 0 1 R _ (by decide)
  | succ i ih =>
    rw [show i + 1 + 1 + d = (i + 1 + d) + 1 by omega, copies_succ, copies_succ]
    simp only [List.cons_append, List.append_assoc]
    exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, ih⟩)

/-- `X⌢L_i⌢L_(j+1) [n] = X⌢L_i⌢0⌢(1^j⌢0)^n` for `i ≤ j` (`i = 0` is `Z`), after every
prefix `Y`: the head of the last `L_(j+1)` is chosen. -/
theorem fs_L_after_L (Y : List ℕ) (i j n : ℕ) (hij : i ≤ j) :
    cut (Y ++ 0 :: copies [1] i ++ 0 :: copies [1] (j+1)) = Y.length + i + 2 ∧
    fs (Y ++ 0 :: copies [1] i ++ 0 :: copies [1] (j+1)) n =
      Y ++ 0 :: copies [1] i ++ [0] ++ copies (copies [1] j ++ [0]) n := by
  have hlt' : copies [1] i ++ 0 :: copies [1] (j+1) < copies [1] (j+1) := by
    have := ones_zero_lt i (j - i) (copies [1] (j+1))
    rwa [show i + 1 + (j - i) = j + 1 by omega] at this
  have h := fs_L_core Y (copies [1] i) 0 j
    (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, hlt'⟩))
    (geAll_ones i _ ⟨_, rfl⟩)
    ⟨fun _ => hlt'.le, tailsLe_ones _ _ _ _ le_rfl⟩ n
  refine ⟨h.1.trans ?_, h.2⟩
  simp [copies_length]

/-- `X⌢Z⌢L_(j+1) [n] = X⌢Z⌢0⌢(1^j⌢0)^n`, after every prefix `Y`. -/
theorem fs_L_after_Z (Y : List ℕ) (j n : ℕ) :
    fs (Y ++ [0] ++ 0 :: copies [1] (j+1)) n =
      Y ++ [0] ++ [0] ++ copies (copies [1] j ++ [0]) n := by
  simpa [copies] using (fs_L_after_L Y 0 j n (Nat.zero_le _)).2

end SSOS.Seq
