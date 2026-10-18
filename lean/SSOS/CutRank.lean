import SSOS.BinarySearch
import SSOS.ShapeExpansion

/-!
# The cut through suffix ranks (§20 of the 2026-10-17 notes)

Every statement here holds for every sequence: no standardness, any entries.

* `mbp_eq_iff`: `mbp S x` is the position `r ≥ x` of the largest suffix `suf S (r+1)` among the
  candidates `x ≤ j < L` with `S_j < S_L`, or `L` when there is no candidate.
* `suf_lt_last_iff`, `p_one_eq_last`: `p 1` is the last position with a smaller entry than `S_L`.
* `breakAt_iff`: `br` stops at the first stage `i ≥ 2` where the record stays
  (`fbp i = fbp (i-1)`), or where an entry `≤ S_(p i)` lies in `(p i, fbp i]`.
* `br_eq_find`: `br` with `breakAt` replaced by that condition.
-/

namespace SSOS.Seq

theorem suf_succ_inj (S : Sequence) (a b : ℕ) (ha : a ≤ S.length) (hb : b ≤ S.length)
    (h : suf S (a+1) = suf S (b+1)) : a = b := by
  have := congrArg List.length h
  rw [suf_length, suf_length] at this
  omega

theorem nil_le_list (l : List ℕ) : ([] : List ℕ) ≤ l := by
  simpa using lex_le_append [] l

/-- A candidate maximizing the suffix is the scan's result. -/
theorem mbp_eq_of_argmax (S : Sequence) (x r : ℕ) (hxr : x ≤ r) (hr : Candidate S r)
    (hbest : ∀ j, x ≤ j → Candidate S j → suf S (j+1) ≤ suf S (r+1)) :
    mbp S x = r := by
  have hs := mbp_spec S x
  have hc := mbp_candidate_of_exists S x r hxr hr
  have hxm : x ≤ mbp S x := by have := hs.1; have := hr.1; omega
  have h1 := (hs.2.2.2 r hxr hr).1
  have h2 := hbest (mbp S x) hxm hc
  exact (suf_succ_inj S _ _ hr.1.le hc.1.le (le_antisymm h1 h2)).symm

/-- §20: `m_x = argmax { r_(j+1) : x ≤ j < L, S_j < S_L }`, or `L` without candidates. -/
theorem mbp_eq_iff (S : Sequence) (x r : ℕ) :
    mbp S x = r ↔
      (x ≤ r ∧ Candidate S r ∧ ∀ j, x ≤ j → Candidate S j → suf S (j+1) ≤ suf S (r+1)) ∨
      (r = S.length ∧ ∀ j, x ≤ j → ¬Candidate S j) := by
  constructor
  · rintro rfl
    by_cases hex : ∃ j, x ≤ j ∧ Candidate S j
    · obtain ⟨j, hxj, hj⟩ := hex
      have hc := mbp_candidate_of_exists S x j hxj hj
      have hs := mbp_spec S x
      refine Or.inl ⟨?_, hc, fun i hi hci => (hs.2.2.2 i hi hci).1⟩
      have := hs.1; have := hc.1; omega
    · push Not at hex
      have hs := (mbp_spec S x).2.2.1
      rcases hs with he | hc
      · exact Or.inr ⟨he, hex⟩
      · have hxm : x ≤ mbp S x := by have := (mbp_spec S x).1; have := hc.1; omega
        exact absurd hc (hex _ hxm)
  · rintro (⟨hxr, hr, hbest⟩ | ⟨rfl, hno⟩)
    · exact mbp_eq_of_argmax S x r hxr hr hbest
    · rcases (mbp_spec S x).2.2.1 with he | hc
      · exact he
      · have hxm : x ≤ mbp S x := by have := (mbp_spec S x).1; have := hc.1; omega
        exact absurd hc (hno _ hxm)

/-- A wider candidate range gives a larger record. -/
theorem mbp_suf_mono (S : Sequence) (x y : ℕ) (hxy : x ≤ y) :
    suf S (mbp S y + 1) ≤ suf S (mbp S x + 1) := by
  rcases (mbp_spec S y).2.2.1 with he | hc
  · rw [he, suf_end]; exact nil_le_list _
  · have hym : y ≤ mbp S y := by have := (mbp_spec S y).1; have := hc.1; omega
    exact ((mbp_spec S x).2.2.2 _ (by omega) hc).1

theorem sp_le_self (S : Sequence) (x : ℕ) (hx : 1 ≤ x) : sp S x ≤ x := by
  rcases Nat.lt_or_ge 1 x with h | h
  · exact (sp_lt S x h).le
  · exact (sp_le_iff S x x).2 ⟨hx, fun i _ hi _ => by omega⟩

theorem p_bounds (S : Sequence) (hL : 1 ≤ S.length) (i : ℕ) :
    1 ≤ p S i ∧ p S i ≤ S.length := by
  induction i with
  | zero => simp [p]; exact hL
  | succ i ih =>
    rw [p_succ]
    exact ⟨one_le_sp S _, (sp_le_self S _ ih.1).trans ih.2⟩

theorem p_succ_le (S : Sequence) (hL : 1 ≤ S.length) (i : ℕ) : p S (i+1) ≤ p S i := by
  rw [p_succ]
  exact sp_le_self S _ (p_bounds S hL i).1

theorem fbp_le_length (S : Sequence) (i : ℕ) : fbp S i ≤ S.length :=
  (mbp_bounds S _).2

/-- §20: the first condition of `breakAt` is "the record stays". -/
theorem breakAt_iff (S : Sequence) (hL : 1 ≤ S.length) (i : ℕ) (hi : 1 ≤ i) :
    breakAt S i ↔ fbp S i = fbp S (i-1) ∨
      ∃ j, p S i < j ∧ j ≤ fbp S i ∧ entry S j ≤ entry S (p S i) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k+1 := ⟨i-1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hmono : suf S (fbp S k + 1) ≤ suf S (fbp S (k+1) + 1) :=
    mbp_suf_mono S _ _ (p_succ_le S hL k)
  unfold breakAt
  simp only [Nat.add_sub_cancel, List.mem_range]
  apply or_congr
  · constructor
    · intro h
      exact suf_succ_inj S _ _ (fbp_le_length S _) (fbp_le_length S _) (le_antisymm h hmono)
    · intro h; rw [h]
  · constructor
    · rintro ⟨j, hj, hpj, he⟩; exact ⟨j, hpj, by omega, he⟩
    · rintro ⟨j, hpj, hj, he⟩; exact ⟨j, by omega, hpj, he⟩

/-- The stopping condition of §20: the record stays, or a low entry lies in `(p i, fbp i]`. -/
def stopAt (S : Sequence) (i : ℕ) : Prop :=
  fbp S i = fbp S (i-1) ∨
    ∃ j ∈ List.range (fbp S i + 1), p S i < j ∧ entry S j ≤ entry S (p S i)

instance (S : Sequence) (i : ℕ) : Decidable (stopAt S i) := by
  unfold stopAt
  infer_instance

/-- §20: `br` with the record condition in place of the suffix comparison. -/
theorem br_eq_find (S : Sequence) (hL : 1 ≤ S.length) :
    br S = ((List.range (S.length+1)).find? fun i => 1 < i ∧ stopAt S i).getD
      S.length := by
  unfold br
  congr 2
  funext i
  apply decide_eq_decide.mpr
  unfold stopAt
  constructor
  · rintro ⟨h1, hb⟩
    refine ⟨h1, ?_⟩
    rcases (breakAt_iff S hL i (by omega)).1 hb with h | ⟨j, hpj, hj, he⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, by simp; omega, hpj, he⟩
  · rintro ⟨h1, h | ⟨j, hj, hpj, he⟩⟩
    · exact ⟨h1, (breakAt_iff S hL i (by omega)).2 (Or.inl h)⟩
    · simp only [List.mem_range] at hj
      exact ⟨h1, (breakAt_iff S hL i (by omega)).2 (Or.inr ⟨j, hpj, by omega, he⟩)⟩

/-- `br S = i` when stage `i` is the first stage `≥ 2` that stops. -/
theorem br_eq_of_first (S : Sequence) (i : ℕ) (hiL : i ≤ S.length) (h1 : 1 < i)
    (hb : breakAt S i) (hno : ∀ k, 1 < k → k < i → ¬breakAt S k) : br S = i := by
  have hf : ((List.range (S.length+1)).find? fun i => 1 < i ∧ breakAt S i) = some i := by
    apply List.find?_range_eq_some.mpr
    refine ⟨by simpa using And.intro h1 hb, by simp; omega, ?_⟩
    intro j hj
    try simp only [List.mem_range] at hj
    by_cases hj1 : 1 < j
    · simp [hj1, hno j hj1 hj]
    · simp [hj1]
  unfold br
  rw [hf]
  rfl

theorem sp_eq_of (S : Sequence) (x a : ℕ) (h1 : 1 ≤ a) (hax : a < x)
    (hlt : suf S a < suf S x) (hgap : ∀ i, a < i → i < x → ¬suf S i < suf S x) :
    sp S x = a := by
  apply le_antisymm
  · refine (sp_le_iff S x a).2 ⟨h1, fun i hi hix hs => ?_⟩
    by_contra hai
    exact hgap i (by omega) hix hs
  · exact le_sp S x a h1 hax hlt

/-- The one-entry last suffix is beaten exactly by the smaller entries. -/
theorem suf_lt_last_iff (S : Sequence) (i : ℕ) (hi : 1 ≤ i) (hiL : i < S.length) :
    suf S i < suf S S.length ↔ entry S i < entry S S.length := by
  rw [suf_cons S i hi hiL.le, suf_cons S S.length (by omega) le_rfl, suf_end,
    List.cons_lt_cons_iff]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact h
    · exact absurd h (List.not_lt_nil _)
  · exact Or.inl

/-- §20: `p 1` is the last position before `L` whose entry is smaller than `S_L`. -/
theorem p_one_eq_last (S : Sequence) (j : ℕ) (h1 : 1 ≤ j) (hj : j < S.length)
    (hjv : entry S j < entry S S.length)
    (hgap : ∀ i, j < i → i < S.length → entry S S.length ≤ entry S i) : p S 1 = j := by
  rw [p_one_eq_sp]
  apply sp_eq_of S _ j h1 hj ((suf_lt_last_iff S j h1 hj).2 hjv)
  intro i hji hiL hs
  have := (suf_lt_last_iff S i (by omega) hiL).1 hs
  have := hgap i hji hiL
  omega

end SSOS.Seq
