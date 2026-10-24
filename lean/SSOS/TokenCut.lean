import SSOS.CutRank

/-!
# The cut of the token laws (§21.2 of the 2026-10-17 notes)

Tokens after `(0,0,2,1)`: `A_k = (0,1,2)⌢(0,2)^k`, `W = (0,1,2,1)`, `E = (0,1,2,0,2,1)`.
The laws for a last token `A0`, `E` or `W` hold after every prefix `X`, standard or not:
the parent path, the records, `br` and the cut lie inside the last unit.

* `cut_A0`, `fs_A0`: `X⌢A0 [n] = X⌢(0,1)⌢1^n`.
* `cut_E`, `fs_E`: `X⌢E [n] = X⌢A_n⌢0` (law L_E).

Positions are one-based as in `Def`. The lemmas `sp_dec` and `mbp_dec` turn a search into
comparisons of suffix lists (`GeAll`, `TailsLe`), so no index arithmetic is left in the laws.
-/

namespace SSOS.Seq

/-- Every tail after an entry `< h` of `A`, continued by `B`, is at most `M`. -/
def TailsLe (h : ℕ) (M : List ℕ) : List ℕ → List ℕ → Prop
  | [], _ => True
  | c :: A, B => (c < h → A ++ B ≤ M) ∧ TailsLe h M A B

/-- Every suffix that starts inside `A`, continued by `B`, is at least `M`. -/
def GeAll (M : List ℕ) : List ℕ → List ℕ → Prop
  | [], _ => True
  | c :: A, B => M ≤ c :: (A ++ B) ∧ GeAll M A B

theorem tailsLe_append (h : ℕ) (M A A' B : List ℕ) :
    TailsLe h M (A ++ A') B ↔ TailsLe h M A (A' ++ B) ∧ TailsLe h M A' B := by
  induction A with
  | nil => simp [TailsLe]
  | cons c A ih => simp [TailsLe, ih, and_assoc]

theorem geAll_append (M A A' B : List ℕ) :
    GeAll M (A ++ A') B ↔ GeAll M A (A' ++ B) ∧ GeAll M A' B := by
  induction A with
  | nil => simp [GeAll]
  | cons c A ih => simp [GeAll, ih, and_assoc]

theorem tailsLe_spec (h : ℕ) (M A B : List ℕ) :
    TailsLe h M A B ↔ ∀ i (hi : i < A.length), A[i] < h → A.drop (i+1) ++ B ≤ M := by
  induction A with
  | nil => simp [TailsLe]
  | cons c A ih =>
    simp only [TailsLe, ih, List.length_cons]
    constructor
    · rintro ⟨h0, hr⟩ i hi hA
      cases i with
      | zero => simpa using h0 (by simpa using hA)
      | succ i => simpa using hr i (by omega) (by simpa using hA)
    · intro H
      exact ⟨fun hc => by simpa using H 0 (by simp) (by simpa using hc),
        fun i hi hA => by simpa using H (i+1) (by omega) (by simpa using hA)⟩

theorem geAll_spec (M A B : List ℕ) :
    GeAll M A B ↔ ∀ i, i < A.length → M ≤ A.drop i ++ B := by
  induction A with
  | nil => simp [GeAll]
  | cons c A ih =>
    simp only [GeAll, ih, List.length_cons]
    constructor
    · rintro ⟨h0, hr⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ i => simpa using hr i (by omega)
    · intro H
      exact ⟨by simpa using H 0 (by simp), fun i hi => by simpa using H (i+1) (by omega)⟩

theorem entry_app (Y T : List ℕ) (k : ℕ) (hk : k < T.length) :
    entry (Y ++ T) (Y.length + k + 1) = T[k] := by
  simp [entry, List.getElem?_append_right, List.getElem?_eq_getElem hk]

theorem suf_app (Y T : List ℕ) (k : ℕ) : suf (Y ++ T) (Y.length + k + 1) = T.drop k := by
  simp [suf, List.drop_append]

theorem entry_last (S l : List ℕ) (h : ℕ) (hS : S = l ++ [h]) : entry S S.length = h := by
  subst hS
  simp [entry]

/-- `sp` from suffix lists: position `|Y|+1` holds `c`, the gap `A` follows, and `B` starts
at `x`. -/
theorem sp_dec (S Y A B : List ℕ) (c x a : ℕ) (hS : S = Y ++ c :: (A ++ B))
    (hx : x = Y.length + A.length + 2) (ha : a = Y.length + 1)
    (hlt : c :: (A ++ B) < B) (hgap : GeAll B A B) : sp S x = a := by
  subst hS hx ha
  have hsa : suf (Y ++ c :: (A ++ B)) (Y.length + 1) = c :: (A ++ B) := by
    simpa using suf_app Y (c :: (A ++ B)) 0
  have hsx : suf (Y ++ c :: (A ++ B)) (Y.length + A.length + 2) = B := by
    have := suf_app Y (c :: (A ++ B)) (A.length + 1)
    rw [show Y.length + (A.length + 1) + 1 = Y.length + A.length + 2 by omega] at this
    rw [this]
    simp
  apply sp_eq_of _ _ _ (by omega) (by omega) (by rw [hsa, hsx]; exact hlt)
  intro i hai hix hs
  obtain ⟨k, rfl⟩ : ∃ k, i = Y.length + (k+1) + 1 := ⟨i - Y.length - 2, by omega⟩
  rw [suf_app, hsx, List.drop_succ_cons, List.drop_append_of_le_length (by omega)] at hs
  exact absurd hs (not_lt_of_ge ((geAll_spec B A B).1 hgap k (by omega)))

/-- `mbp` from suffix lists: the scan starts at `|Y|+1` and picks `c`, followed by `M`. -/
theorem mbp_dec (S Y D M : List ℕ) (c h x r : ℕ) (hS : S = Y ++ (D ++ c :: M))
    (hx : x = Y.length + 1) (hr : r = Y.length + D.length + 1) (hM : M ≠ [])
    (hh : entry S S.length = h) (hc : c < h) (hT : TailsLe h M (D ++ c :: M) []) :
    mbp S x = r := by
  subst hx hr
  have hlen : S.length = Y.length + D.length + 1 + M.length := by
    subst hS; simp; omega
  have hMl : 1 ≤ M.length := List.length_pos_iff.mpr hM
  have hsr : suf S (Y.length + D.length + 1 + 1) = M := by
    rw [hS, show Y.length + D.length + 1 + 1 = Y.length + (D.length + 1) + 1 by omega, suf_app]
    simp [List.drop_append]
  apply mbp_eq_of_argmax _ _ _ (by omega)
  · refine ⟨by omega, ?_⟩
    rw [hh, hS, entry_app _ _ _ (by simp)]
    simpa using hc
  · intro j hj hcan
    obtain ⟨k, rfl⟩ : ∃ k, j = Y.length + k + 1 := ⟨j - Y.length - 1, by omega⟩
    have hk : k < (D ++ c :: M).length := by have := hcan.1; simp at *; omega
    have he := hcan.2
    rw [hh, hS, entry_app _ _ _ hk] at he
    rw [hsr, hS, show Y.length + k + 1 + 1 = Y.length + (k+1) + 1 by omega, suf_app]
    simpa using (tailsLe_spec h M _ []).1 hT k hk he

theorem breakAt_two_of_eq (S : Sequence) (h : fbp S 2 = fbp S 1) : breakAt S 2 :=
  Or.inl (by rw [show (2:ℕ) - 1 = 1 by rfl, h])

theorem breakAt_two_of_low (S : Sequence) (j : ℕ) (hpj : p S 2 < j) (hj : j ≤ fbp S 2)
    (he : entry S j ≤ entry S (p S 2)) : breakAt S 2 :=
  Or.inr ⟨j, List.mem_range.mpr (by omega), hpj, he⟩

/-! ## The tokens -/

def tA (k : ℕ) : List ℕ := [0,1,2] ++ copies [0,2] k
def tW : List ℕ := [0,1,2,1]
def tE : List ℕ := [0,1,2,0,2,1]

theorem copies_succ (s : List ℕ) (k : ℕ) : copies s (k+1) = s ++ copies s k := by
  simp [copies, List.replicate_succ]

theorem copies_succ' (s : List ℕ) (k : ℕ) : copies s (k+1) = copies s k ++ s := by
  simp [copies, List.replicate_succ']

theorem copies_add (s : List ℕ) (a b : ℕ) : copies s (a+b) = copies s a ++ copies s b := by
  simp only [copies, List.replicate_add, List.flatten_append]

/-- Rotation of a repeated word. -/
theorem copies_rotate (u v : List ℕ) (n : ℕ) :
    v ++ copies (u ++ v) n = copies (v ++ u) n ++ v := by
  induction n with
  | zero => simp [copies]
  | succ n ih =>
    rw [copies_succ, copies_succ]
    simp only [List.append_assoc]
    rw [ih]

theorem copies_length (s : List ℕ) (k : ℕ) : (copies s k).length = k * s.length := by
  induction k with
  | zero => simp [copies]
  | succ k ih => rw [copies_succ, List.length_append, ih, Nat.succ_mul]; omega

/-- The expansion once the cut is known: `G` is kept and `R⌢(h-1)` is repeated. -/
theorem fs_of_cut_word (S G R : List ℕ) (h : ℕ) (hS : S = G ++ R ++ [h]) (hh : 0 < h)
    (hc : cut S = G.length) (n : ℕ) : fs S n = G ++ copies (R ++ [h-1]) n := by
  have hl : entry S S.length = h := entry_last S (G ++ R) h (by simp [hS])
  have hne : S.isEmpty = false := by subst hS; simp
  simp only [fs, hne, hl, good, bad, hc, Bool.false_eq_true, if_false,
    show (h = 0) = False from propext ⟨by omega, False.elim⟩]
  subst hS
  simp [copies, List.append_assoc]

/-! ## Last token `A0` -/

theorem cut_A0 (X : List ℕ) :
    p (X ++ [0,1,2]) 1 = X.length + 2 ∧ p (X ++ [0,1,2]) 2 = X.length + 1 ∧
    br (X ++ [0,1,2]) = 2 ∧ cut (X ++ [0,1,2]) = X.length + 2 := by
  set S := X ++ [0,1,2] with hSdef
  have hL : S.length = X.length + 3 := by simp [S]
  have hh : entry S S.length = 2 := entry_last S (X ++ [0,1]) 2 (by simp [S])
  have hp1 : p S 1 = X.length + 2 := by
    rw [p_one_eq_sp, hL]
    exact sp_dec S (X ++ [0]) [] [2] 1 (X.length + 3) (X.length + 2) (by simp [S]) (by simp)
      (by simp) (by decide) (by simp [GeAll])
  have hp2 : p S 2 = X.length + 1 := by
    rw [p_succ, hp1]
    exact sp_dec S X [] [1,2] 0 (X.length + 2) (X.length + 1) (by simp [S]) (by simp) rfl
      (by decide) (by simp [GeAll])
  have hm1 : mbp S (X.length + 2) = X.length + 2 :=
    mbp_dec S (X ++ [0]) [] [2] 1 2 (X.length + 2) (X.length + 2) (by simp [S]) (by simp)
      (by simp) (by simp) hh
      (by decide) (by simp only [TailsLe, List.cons_append, List.nil_append]; decide)
  have hm2 : mbp S (X.length + 1) = X.length + 2 :=
    mbp_dec S X [0] [2] 1 2 (X.length + 1) (X.length + 2) (by simp [S]) rfl (by simp) (by simp) hh
      (by decide) (by simp only [TailsLe, List.cons_append, List.nil_append]; decide)
  have hf1 : fbp S 1 = X.length + 2 := by simp only [fbp, hp1, hm1]
  have hf2 : fbp S 2 = X.length + 2 := by simp only [fbp, hp2, hm2]
  have hbr : br S = 2 := br_eq_two_of_breakAt S (by omega) (breakAt_two_of_eq S (by rw [hf1, hf2]))
  exact ⟨hp1, hp2, hbr, by rw [cut, hbr, hf2]⟩

theorem fs_A0 (X : List ℕ) (n : ℕ) :
    fs (X ++ [0,1,2]) n = X ++ [0,1] ++ copies [1] n := by
  have h := fs_of_cut_word (X ++ [0,1,2]) (X ++ [0,1]) [] 2 (by simp) (by decide)
    (by rw [(cut_A0 X).2.2.2]; simp) n
  simpa using h

/-! ## Last token `E` (law L_E) -/

theorem cut_E (X : List ℕ) :
    p (X ++ tE) 1 = X.length + 4 ∧ p (X ++ tE) 2 = X.length + 1 ∧
    br (X ++ tE) = 2 ∧ cut (X ++ tE) = X.length + 4 := by
  set S := X ++ tE with hSdef
  have hL : S.length = X.length + 6 := by simp [S, tE]
  have hh : entry S S.length = 1 := entry_last S (X ++ [0,1,2,0,2]) 1 (by simp [S, tE])
  have hp1 : p S 1 = X.length + 4 := by
    rw [p_one_eq_sp, hL]
    exact sp_dec S (X ++ [0,1,2]) [2] [1] 0 (X.length + 6) (X.length + 4) (by simp [S, tE])
      (by simp) (by simp)
      (by decide) (by simp only [GeAll]; decide)
  have hp2 : p S 2 = X.length + 1 := by
    rw [p_succ, hp1]
    exact sp_dec S X [1,2] [0,2,1] 0 (X.length + 4) (X.length + 1) (by simp [S, tE]) (by simp)
      rfl (by decide)
      (by simp only [GeAll]; decide)
  have hm1 : mbp S (X.length + 4) = X.length + 4 :=
    mbp_dec S (X ++ [0,1,2]) [] [2,1] 0 1 (X.length + 4) (X.length + 4) (by simp [S, tE])
      (by simp) (by simp) (by simp)
      hh (by decide) (by simp only [TailsLe, List.cons_append, List.nil_append]; decide)
  have hm2 : mbp S (X.length + 1) = X.length + 4 :=
    mbp_dec S X [0,1,2] [2,1] 0 1 (X.length + 1) (X.length + 4) (by simp [S, tE]) rfl (by simp)
      (by simp) hh
      (by decide) (by simp only [TailsLe, List.cons_append, List.nil_append]; decide)
  have hf1 : fbp S 1 = X.length + 4 := by simp only [fbp, hp1, hm1]
  have hf2 : fbp S 2 = X.length + 4 := by simp only [fbp, hp2, hm2]
  have hbr : br S = 2 := br_eq_two_of_breakAt S (by omega) (breakAt_two_of_eq S (by rw [hf1, hf2]))
  exact ⟨hp1, hp2, hbr, by rw [cut, hbr, hf2]⟩

theorem fs_E (X : List ℕ) (n : ℕ) : fs (X ++ tE) n = X ++ tA n ++ [0] := by
  have h := fs_of_cut_word (X ++ tE) (X ++ [0,1,2,0]) [2] 1 (by simp [tE]) (by decide)
    (by rw [(cut_E X).2.2.2]; simp) n
  rw [h, tA]
  have hrot := copies_rotate [2] [0] n
  simp only [List.cons_append, List.nil_append] at hrot
  simp only [Nat.sub_self, List.append_assoc, List.cons_append, List.nil_append]
  rw [show (0 :: copies [2, 0] n) = [0] ++ copies ([2] ++ [0]) n by rfl, copies_rotate]
  rfl

/-! ## Last token `W` (law L_W) -/

theorem cons_le_of_lt (a b : ℕ) (l r : List ℕ) (h : a < b) : a :: l ≤ b :: r :=
  (List.cons_lt_cons_iff.mpr (Or.inl h)).le

theorem cons_lt_of_lt (a b : ℕ) (l r : List ℕ) (h : a < b) : a :: l < b :: r :=
  List.cons_lt_cons_iff.mpr (Or.inl h)

theorem append_lt_append_left (P a b : List ℕ) (h : a < b) : P ++ a < P ++ b := by
  induction P with
  | nil => simpa using h
  | cons c P ih =>
    simp only [List.cons_append]
    exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, ih⟩)

theorem append_le_append_left (P a b : List ℕ) (h : a ≤ b) : P ++ a ≤ P ++ b := by
  rcases lt_or_eq_of_le h with h | h
  · exact (append_lt_append_left P a b h).le
  · rw [h]

/-- Entry of a decomposed sequence. -/
theorem entry_at (S Y T : List ℕ) (k i : ℕ) (hS : S = Y ++ T) (hi : i = Y.length + k + 1)
    (hk : k < T.length) : entry S i = T[k] := by
  subst hS hi; exact entry_app Y T k hk

/-- Every suffix inside a run of `W` is at least `W`. -/
theorem geAll_copies_W (j : ℕ) (B : List ℕ) : GeAll tW (copies tW j) B := by
  induction j generalizing B with
  | zero => simp [copies, GeAll]
  | succ j ih =>
    rw [copies_succ, geAll_append]
    refine ⟨?_, ih B⟩
    simp only [tW, GeAll, List.cons_append, List.nil_append]
    refine ⟨?_, cons_le_of_lt _ _ _ _ (by decide), cons_le_of_lt _ _ _ _ (by decide),
      cons_le_of_lt _ _ _ _ (by decide), trivial⟩
    simpa [tW] using lex_le_append [0,1,2,1] (copies tW j ++ B)

/-- The zeros of a run of `W` are followed by `1`, below any tail that starts with `2`. -/
theorem tailsLe_copies_W_two (j : ℕ) (N B : List ℕ) : TailsLe 1 (2 :: N) (copies tW j) B := by
  induction j generalizing B with
  | zero => simp [copies, TailsLe]
  | succ j ih =>
    rw [copies_succ, tailsLe_append]
    refine ⟨?_, ih B⟩
    simp only [tW, TailsLe, List.cons_append, List.nil_append]
    exact ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide), by omega, by omega, by omega, trivial⟩

/-- Core of L_W. The last unit is `(0,1,2)⌢Q`, followed by the last `W`;
`Q⌢W = 0 :: M` and `M` is the tail after the first zero of `Q⌢W`. -/
theorem cut_W_core (X Q M : List ℕ) (hQM : Q ++ tW = 0 :: M) (hgapQ : GeAll tW Q tW)
    (hM1 : 1 :: 2 :: 0 :: M ≤ M) (hM2 : TailsLe 1 M M []) :
    p (X ++ [0,1,2] ++ Q ++ tW) 2 = X.length + 1 ∧ br (X ++ [0,1,2] ++ Q ++ tW) = 2 ∧
    cut (X ++ [0,1,2] ++ Q ++ tW) = X.length + 4 := by
  set S := X ++ [0,1,2] ++ Q ++ tW with hSdef
  have hL : S.length = X.length + Q.length + 7 := by simp [S, tW]; omega
  have hh : entry S S.length = 1 := entry_last S (X ++ [0,1,2] ++ Q ++ [0,1,2]) 1 (by simp [S, tW])
  have hS' : S = X ++ ([0,1,2] ++ 0 :: M) := by simp [S, ← hQM]
  have hMl : M.length = Q.length + 3 := by
    have := congrArg List.length hQM; simp [tW] at this; omega
  have hp1 : p S 1 = X.length + Q.length + 4 := by
    rw [p_one_eq_sp, hL]
    exact sp_dec S (X ++ [0,1,2] ++ Q) [1,2] [1] 0 _ _ (by simp [S, tW]) (by simp; omega)
      (by simp; omega) (by decide) (by simp only [GeAll, List.cons_append, List.nil_append]; decide)
  have hp2 : p S 2 = X.length + 1 := by
    rw [p_succ, hp1]
    refine sp_dec S X ([1,2] ++ Q) tW 0 _ _ (by simp [S]) (by simp; omega) rfl ?_ ?_
    · rw [List.append_assoc, hQM]
      simp only [tW, List.cons_append, List.nil_append]
      exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl,
        List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)⟩)⟩)
    · rw [geAll_append]
      refine ⟨?_, hgapQ⟩
      simp only [tW, GeAll, List.cons_append, List.nil_append]
      exact ⟨cons_le_of_lt _ _ _ _ (by decide), cons_le_of_lt _ _ _ _ (by decide), trivial⟩
  have hm1 : mbp S (X.length + Q.length + 4) = X.length + Q.length + 4 :=
    mbp_dec S (X ++ [0,1,2] ++ Q) [] [1,2,1] 0 1 _ _ (by simp [S, tW]) (by simp; omega)
      (by simp; omega) (by simp) hh (by decide)
      (by simp only [TailsLe, List.cons_append, List.nil_append]; decide)
  have hm2 : mbp S (X.length + 1) = X.length + 4 := by
    refine mbp_dec S X [0,1,2] M 0 1 _ _ hS' rfl (by simp) ?_ hh (by decide) ?_
    · intro hn; rw [hn] at hMl; simp at hMl
    · rw [tailsLe_append]
      simp only [TailsLe, List.cons_append, List.nil_append, List.append_nil]
      exact ⟨⟨fun _ => hM1, by omega, by omega, trivial⟩, fun _ => le_rfl, hM2⟩
  have hf1 : fbp S 1 = X.length + Q.length + 4 := by simp only [fbp, hp1, hm1]
  have hf2 : fbp S 2 = X.length + 4 := by simp only [fbp, hp2, hm2]
  have he4 : entry S (X.length + 4) = 0 :=
    entry_at S (X ++ [0,1,2]) (0 :: M) 0 _ (by rw [hS']; simp) (by simp) (by simp)
  have he1 : entry S (X.length + 1) = 0 :=
    entry_at S X ([0,1,2] ++ 0 :: M) 0 _ hS' rfl (by simp)
  have hbr : br S = 2 := br_eq_two_of_breakAt S (by omega)
    (breakAt_two_of_low S (X.length + 4) (by omega) (by omega) (by rw [hp2, he4, he1]))
  exact ⟨hp2, hbr, by rw [cut, hbr, hf2]⟩

theorem fs_W_core (X Q M : List ℕ) (hQM : Q ++ tW = 0 :: M) (hgapQ : GeAll tW Q tW)
    (hM1 : 1 :: 2 :: 0 :: M ≤ M) (hM2 : TailsLe 1 M M []) (n : ℕ) :
    fs (X ++ [0,1,2] ++ Q ++ tW) n = X ++ copies ([0,1,2] ++ Q) n ++ [0,1,2,0] := by
  have hc := (cut_W_core X Q M hQM hgapQ hM1 hM2).2.2
  have hQ3 : Q ++ [0,1,2] = 0 :: M.dropLast := by
    have hMne : M ≠ [] := by
      intro hn; rw [hn] at hQM; have := congrArg List.length hQM; simp [tW] at this
    have := congrArg List.dropLast hQM
    rw [tW, List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hMne] at this
    simpa using this
  have hS : X ++ [0,1,2] ++ Q ++ tW = (X ++ [0,1,2,0]) ++ M.dropLast ++ [1] := by
    rw [show tW = [0,1,2] ++ [1] from rfl]
    simp only [List.append_assoc]
    rw [← List.append_assoc Q [0,1,2] [1], hQ3]
    simp
  rw [fs_of_cut_word _ (X ++ [0,1,2,0]) M.dropLast 1 hS (by decide) (by rw [hc]; simp) n]
  have h1 := copies_rotate M.dropLast [0] n
  have h2 := copies_rotate Q [0,1,2] n
  simp only [List.singleton_append] at h1
  rw [← hQ3] at h1
  simp only [Nat.sub_self, List.append_assoc]
  rw [show [0,1,2,0] ++ copies (M.dropLast ++ [0]) n
      = [0,1,2] ++ ([0] ++ copies (M.dropLast ++ [0]) n) by simp, copies_rotate,
    show [0] ++ M.dropLast = Q ++ [0,1,2] by rw [hQ3]; rfl, ← List.append_assoc [0,1,2], h2]
  simp

theorem geAll_copies_02 (j : ℕ) (B : List ℕ) : GeAll tW (copies [0,2] j) B := by
  induction j generalizing B with
  | zero => simp [copies, GeAll]
  | succ j ih =>
    rw [copies_succ, geAll_append]
    refine ⟨?_, ih B⟩
    simp only [tW, GeAll, List.cons_append, List.nil_append]
    exact ⟨(List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)).le,
      cons_le_of_lt _ _ _ _ (by decide), trivial⟩

theorem cons_le_cons_same (c : ℕ) (a b : List ℕ) (h : a ≤ b) : c :: a ≤ c :: b := by
  simpa using append_le_append_left [c] a b h

/-- The tails after the zeros of `(0,2)^k` grow with the number of remaining `(0,2)`. -/
theorem tailsLe_copies_02 (V' : List ℕ) (k j : ℕ) :
    TailsLe 1 (2 :: (copies [0,2] (j + k) ++ (0 :: 1 :: V'))) (copies [0,2] k) (0 :: 1 :: V') := by
  induction k generalizing j with
  | zero => simp [copies, TailsLe]
  | succ k ih =>
    rw [copies_succ, tailsLe_append]
    refine ⟨?_, by rw [show j + (k+1) = (j+1) + k by omega]; exact ih (j+1)⟩
    simp only [TailsLe, List.cons_append, List.nil_append]
    refine ⟨fun _ => cons_le_cons_same 2 _ _ ?_, by omega, trivial⟩
    rw [show j + (k+1) = k + (j+1) by omega, copies_add, List.append_assoc]
    apply append_le_append_left
    rw [copies_succ]
    exact (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)).le

/-- The tails after the zeros of a run of `W` grow with the number of remaining `W`. -/
theorem tailsLe_copies_W_run (m j : ℕ) :
    TailsLe 1 ([1,2,1] ++ copies tW (j + m)) (copies tW m) [] := by
  induction m generalizing j with
  | zero => simp [copies, TailsLe]
  | succ m ih =>
    rw [copies_succ, tailsLe_append]
    refine ⟨?_, by rw [show j + (m+1) = (j+1) + m by omega]; exact ih (j+1)⟩
    simp only [tW, TailsLe, List.cons_append, List.nil_append, List.append_nil]
    refine ⟨fun _ => ?_, by omega, by omega, by omega, trivial⟩
    rw [show j + (m+1) = m + (j+1) by omega, copies_add]
    have h := append_le_append_left [1,2,1] _ _ (lex_le_append (copies tW m) (copies tW (j+1)))
    simp only [tW] at h ⊢
    simpa using h

theorem tW_lt_02 (R : List ℕ) : tW < 0 :: 2 :: R :=
  List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)

/-- Unit `A_(k+1) W^m` before the last `W`. -/
theorem W_hyps_A (k m : ℕ) :
    let Q := copies [0,2] (k+1) ++ copies tW m
    let M := 2 :: (copies [0,2] k ++ (copies tW m ++ tW))
    Q ++ tW = 0 :: M ∧ GeAll tW Q tW ∧ 1 :: 2 :: 0 :: M ≤ M ∧ TailsLe 1 M M [] := by
  intro Q M
  refine ⟨by simp [Q, M, copies_succ], ?_, cons_le_of_lt _ _ _ _ (by decide), ?_⟩
  · simp only [Q]
    rw [geAll_append]
    exact ⟨geAll_copies_02 _ _, geAll_copies_W _ _⟩
  · simp only [M, TailsLe]
    refine ⟨by omega, ?_⟩
    rw [tailsLe_append]
    refine ⟨?_, ?_⟩
    · have h := tailsLe_copies_02 ([2,1] ++ copies tW m) k 0
      rw [Nat.zero_add] at h
      have hV : copies tW m ++ tW = 0 :: 1 :: ([2,1] ++ copies tW m) := by
        rw [← copies_succ', copies_succ]; simp [tW]
      rw [hV, List.append_nil]
      exact h
    · rw [← copies_succ']
      exact tailsLe_copies_W_two _ _ _

/-- Unit `E W^m` before the last `W`. -/
theorem W_hyps_E (m : ℕ) :
    let Q := [0,2,1] ++ copies tW m
    let M := 2 :: 1 :: (copies tW m ++ tW)
    Q ++ tW = 0 :: M ∧ GeAll tW Q tW ∧ 1 :: 2 :: 0 :: M ≤ M ∧ TailsLe 1 M M [] := by
  intro Q M
  refine ⟨by simp [Q, M], ?_, cons_le_of_lt _ _ _ _ (by decide), ?_⟩
  · simp only [Q]
    rw [geAll_append]
    refine ⟨?_, geAll_copies_W _ _⟩
    simp only [GeAll, List.cons_append, List.nil_append]
    exact ⟨(tW_lt_02 _).le, cons_le_of_lt _ _ _ _ (by decide),
      cons_le_of_lt _ _ _ _ (by decide), trivial⟩
  · simp only [M, TailsLe]
    refine ⟨by omega, by omega, ?_⟩
    rw [← copies_succ']
    exact tailsLe_copies_W_two _ _ _

/-- Unit `A0 W^m` before the last `W`. -/
theorem W_hyps_A0 (m : ℕ) :
    let Q := copies tW m
    let M := [1,2,1] ++ copies tW m
    Q ++ tW = 0 :: M ∧ GeAll tW Q tW ∧ 1 :: 2 :: 0 :: M ≤ M ∧ TailsLe 1 M M [] := by
  intro Q M
  refine ⟨by simp only [Q, M]; rw [← copies_succ', copies_succ]; simp [tW],
    geAll_copies_W _ _, ?_, ?_⟩
  · simp only [M, List.cons_append, List.nil_append]
    exact (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr
      (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)⟩)).le
  · simp only [M, List.cons_append, List.nil_append, TailsLe]
    refine ⟨by omega, by omega, by omega, ?_⟩
    simpa using tailsLe_copies_W_run m 0

/-- L_W, unit `A_(k+1) W^m`: `X⌢A_(k+1)⌢W^m⌢W [n] = X⌢(A_(k+1)⌢W^m)^n⌢A0⌢0`. -/
theorem law_W_A (X : List ℕ) (k m : ℕ) :
    let S := X ++ tA (k+1) ++ copies tW m ++ tW
    p S 2 = X.length + 1 ∧ br S = 2 ∧ cut S = X.length + 4 ∧
    ∀ n, fs S n = X ++ copies (tA (k+1) ++ copies tW m) n ++ [0,1,2,0] := by
  intro S
  obtain ⟨h1, h2, h3, h4⟩ := W_hyps_A k m
  have hS : S = X ++ [0,1,2] ++ (copies [0,2] (k+1) ++ copies tW m) ++ tW := by
    simp [S, tA]
  rw [hS]
  refine ⟨(cut_W_core X _ _ h1 h2 h3 h4).1, (cut_W_core X _ _ h1 h2 h3 h4).2.1,
    (cut_W_core X _ _ h1 h2 h3 h4).2.2, fun n => ?_⟩
  rw [fs_W_core X _ _ h1 h2 h3 h4 n]
  simp [tA]

/-- L_W, unit `E W^m`: `X⌢E⌢W^m⌢W [n] = X⌢(E⌢W^m)^n⌢A0⌢0`. -/
theorem law_W_E (X : List ℕ) (m : ℕ) :
    let S := X ++ tE ++ copies tW m ++ tW
    p S 2 = X.length + 1 ∧ br S = 2 ∧ cut S = X.length + 4 ∧
    ∀ n, fs S n = X ++ copies (tE ++ copies tW m) n ++ [0,1,2,0] := by
  intro S
  obtain ⟨h1, h2, h3, h4⟩ := W_hyps_E m
  have hS : S = X ++ [0,1,2] ++ ([0,2,1] ++ copies tW m) ++ tW := by
    simp [S, tE]
  rw [hS]
  refine ⟨(cut_W_core X _ _ h1 h2 h3 h4).1, (cut_W_core X _ _ h1 h2 h3 h4).2.1,
    (cut_W_core X _ _ h1 h2 h3 h4).2.2, fun n => ?_⟩
  rw [fs_W_core X _ _ h1 h2 h3 h4 n]
  simp [tE]

/-- L_W, unit `A0 W^m`: `X⌢A0⌢W^m⌢W [n] = X⌢(A0⌢W^m)^n⌢A0⌢0`. -/
theorem law_W_A0 (X : List ℕ) (m : ℕ) :
    let S := X ++ tA 0 ++ copies tW m ++ tW
    p S 2 = X.length + 1 ∧ br S = 2 ∧ cut S = X.length + 4 ∧
    ∀ n, fs S n = X ++ copies (tA 0 ++ copies tW m) n ++ [0,1,2,0] := by
  intro S
  obtain ⟨h1, h2, h3, h4⟩ := W_hyps_A0 m
  have hS : S = X ++ [0,1,2] ++ copies tW m ++ tW := by
    simp [S, tA, copies]
  rw [hS]
  refine ⟨(cut_W_core X _ _ h1 h2 h3 h4).1, (cut_W_core X _ _ h1 h2 h3 h4).2.1,
    (cut_W_core X _ _ h1 h2 h3 h4).2.2, fun n => ?_⟩
  rw [fs_W_core X _ _ h1 h2 h3 h4 n]
  simp [tA, copies]

/-- L_W, all tokens `W`: `(0,0,2,1)⌢W^(j+1) [n+1] = (0,0,2,1)⌢W^j⌢(E⌢W^j)^n⌢A0⌢0`.
Here `p 2 = 1` and the cut is `2`. -/
theorem law_W_lead (j : ℕ) :
    let S := [0,0,2,1] ++ copies tW (j+1)
    p S 2 = 1 ∧ br S = 2 ∧ cut S = 2 ∧
    ∀ n, fs S (n+1) = [0,0,2,1] ++ copies tW j ++ copies (tE ++ copies tW j) n ++ [0,1,2,0] := by
  intro S
  have hS : S = [0,0,2,1] ++ copies tW j ++ tW := by simp [S, copies_succ']
  have hL : S.length = 4 * j + 8 := by
    rw [hS]; simp [copies_length, tW]; omega
  have hh : entry S S.length = 1 :=
    entry_last S ([0,0,2,1] ++ copies tW j ++ [0,1,2]) 1 (by rw [hS]; simp [tW])
  have hp1 : p S 1 = 4 * j + 5 := by
    rw [p_one_eq_sp, hL]
    exact sp_dec S ([0,0,2,1] ++ copies tW j) [1,2] [1] 0 _ _ (by rw [hS]; simp [tW])
      (by simp [copies_length, tW]; omega) (by simp [copies_length, tW]; omega) (by decide)
      (by simp only [GeAll, List.cons_append, List.nil_append]; decide)
  have hgap : GeAll tW ([0,2,1] ++ copies tW j) tW := by
    rw [geAll_append]
    refine ⟨?_, geAll_copies_W _ _⟩
    simp only [GeAll, List.cons_append, List.nil_append]
    exact ⟨(tW_lt_02 _).le, cons_le_of_lt _ _ _ _ (by decide),
      cons_le_of_lt _ _ _ _ (by decide), trivial⟩
  have hp2 : p S 2 = 1 := by
    rw [p_succ, hp1]
    exact sp_dec S [] ([0,2,1] ++ copies tW j) tW 0 _ _ (by rw [hS]; simp)
      (by simp [copies_length, tW]; omega) rfl
      (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)) hgap
  have hm1 : mbp S (4 * j + 5) = 4 * j + 5 :=
    mbp_dec S ([0,0,2,1] ++ copies tW j) [] [1,2,1] 0 1 _ _ (by rw [hS]; simp [tW])
      (by simp [copies_length, tW]; omega) (by simp [copies_length, tW]; omega) (by simp) hh (by decide)
      (by simp only [TailsLe, List.cons_append, List.nil_append]; decide)
  have hm2 : mbp S 1 = 2 := by
    refine mbp_dec S [] [0] (2 :: 1 :: copies tW (j+1)) 0 1 _ _ (by simp [S]) rfl rfl
      (by simp) hh (by decide) ?_
    simp only [TailsLe, List.cons_append, List.nil_append, List.append_nil]
    exact ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide), fun _ => le_rfl, by omega, by omega,
      tailsLe_copies_W_two _ _ _⟩
  have hf2 : fbp S 2 = 2 := by simp only [fbp, hp2, hm2]
  have he2 : entry S 2 = 0 := by simp [S, entry]
  have he1 : entry S 1 = 0 := by simp [S, entry]
  have hbr : br S = 2 := br_eq_two_of_breakAt S (by omega)
    (breakAt_two_of_low S 2 (by omega) (by omega) (by rw [hp2, he2, he1]))
  have hc : cut S = 2 := by rw [cut, hbr, hf2]
  refine ⟨hp2, hbr, hc, fun n => ?_⟩
  have hS2 : S = [0,0] ++ ([2,1] ++ copies tW j ++ [0,1,2]) ++ [1] := by
    rw [hS]; simp [tW]
  rw [fs_of_cut_word S [0,0] _ 1 hS2 (by decide) (by rw [hc]; rfl) (n+1), copies_succ]
  have h := copies_rotate ([2,1] ++ copies tW j) [0,1,2,0] n
  simp only [Nat.sub_self, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
  rw [h]
  simp [tE]

/-! ## Last token `A_(k+1)` (law L_A) -/

theorem geAll_copies_02_self (j : ℕ) (B : List ℕ) : GeAll [0,2] (copies [0,2] j) B := by
  induction j generalizing B with
  | zero => simp [copies, GeAll]
  | succ j ih =>
    rw [copies_succ, geAll_append]
    refine ⟨?_, ih B⟩
    simp only [GeAll, List.cons_append, List.nil_append]
    exact ⟨by simpa using lex_le_append [0,2] (copies [0,2] j ++ B),
      cons_le_of_lt _ _ _ _ (by decide), trivial⟩

theorem tailsLe_copies_02_end (k j : ℕ) :
    TailsLe 2 (2 :: copies [0,2] (j + k)) (copies [0,2] k) [] := by
  induction k generalizing j with
  | zero => simp [copies, TailsLe]
  | succ k ih =>
    rw [copies_succ, tailsLe_append]
    refine ⟨?_, by rw [show j + (k+1) = (j+1) + k by omega]; exact ih (j+1)⟩
    simp only [TailsLe, List.cons_append, List.nil_append, List.append_nil]
    refine ⟨fun _ => cons_le_cons_same 2 _ _ ?_, by omega, trivial⟩
    rw [show j + (k+1) = k + (j+1) by omega, copies_add]
    exact lex_le_append _ _

/-- Stage 2 for a last `A_(k+1)`, after every prefix: `p 2` is the head of `A_(k+1)`, its record
is the head `1`, and stage 2 does not stop. -/
theorem stage2_A (X : List ℕ) (k : ℕ) :
    let S := X ++ tA (k+1)
    p S 2 = X.length + 1 ∧ fbp S 2 = X.length + 2 ∧ ¬breakAt S 2 := by
  intro S
  have hL : S.length = X.length + 2 * k + 5 := by simp [S, tA, copies_length]; omega
  have hh : entry S S.length = 2 :=
    entry_last S (X ++ [0,1,2] ++ copies [0,2] k ++ [0]) 2 (by simp [S, tA, copies_succ'])
  have hp1 : p S 1 = X.length + 2 * k + 4 := by
    rw [p_one_eq_sp, hL]
    exact sp_dec S (X ++ [0,1,2] ++ copies [0,2] k) [] [2] 0 _ _
      (by simp [S, tA, copies_succ']) (by simp [copies_length]; omega)
      (by simp [copies_length]; omega) (by decide) (by simp [GeAll])
  have hp2 : p S 2 = X.length + 1 := by
    rw [p_succ, hp1]
    refine sp_dec S X ([1,2] ++ copies [0,2] k) [0,2] 0 _ _ (by simp [S, tA, copies_succ'])
      (by simp [copies_length]; omega) rfl ?_ ?_
    · exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)
    · rw [geAll_append]
      refine ⟨?_, geAll_copies_02_self _ _⟩
      simp only [GeAll, List.cons_append, List.nil_append]
      exact ⟨cons_le_of_lt _ _ _ _ (by decide), cons_le_of_lt _ _ _ _ (by decide), trivial⟩
  have hm1 : mbp S (X.length + 2 * k + 4) = X.length + 2 * k + 4 :=
    mbp_dec S (X ++ [0,1,2] ++ copies [0,2] k) [] [2] 0 2 _ _ (by simp [S, tA, copies_succ'])
      (by simp [copies_length]; omega) (by simp [copies_length]; omega) (by simp) hh
      (by decide) (by simp [TailsLe])
  have hm2 : mbp S (X.length + 1) = X.length + 2 := by
    refine mbp_dec S X [0] (2 :: copies [0,2] (k+1)) 1 2 _ _ (by simp [S, tA]) rfl rfl
      (by simp) hh (by decide) ?_
    simp only [TailsLe, List.cons_append, List.nil_append, List.append_nil]
    refine ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide), fun _ => le_rfl, by omega, ?_⟩
    simpa using tailsLe_copies_02_end (k+1) 0
  have hf1 : fbp S 1 = X.length + 2 * k + 4 := by simp only [fbp, hp1, hm1]
  have hf2 : fbp S 2 = X.length + 2 := by simp only [fbp, hp2, hm2]
  refine ⟨hp2, hf2, ?_⟩
  rw [breakAt_iff S (by omega) 2 (by omega)]
  rintro (h | ⟨j, hpj, hj, he⟩)
  · simp only [show (2:ℕ) - 1 = 1 by rfl, hf1, hf2] at h; omega
  · rw [hp2] at hpj he
    rw [hf2] at hj
    obtain rfl : j = X.length + 2 := by omega
    have : entry S (X.length + 2) = 1 :=
      entry_at S X (tA (k+1)) 1 _ (by simp [S]) rfl (by simp [tA])
    have h0 : entry S (X.length + 1) = 0 :=
      entry_at S X (tA (k+1)) 0 _ (by simp [S]) rfl (by simp [tA])
    omega

theorem br_eq_three (S : Sequence) (hL : 3 ≤ S.length) (h2 : ¬breakAt S 2) (h3 : breakAt S 3) :
    br S = 3 :=
  br_eq_of_first S 3 hL (by omega) h3 (fun k hk1 hk3 => by
    obtain rfl : k = 2 := by omega
    exact h2)

theorem copies_W_head (m : ℕ) (Z : List ℕ) (hZ : ∃ Z', Z = 0 :: Z') :
    ∃ Z'', copies tW m ++ Z = 0 :: Z'' := by
  cases m with
  | zero => simpa [copies] using hZ
  | succ m => exact ⟨[1,2,1] ++ copies tW m ++ Z, by simp [copies_succ, tW]⟩

/-- Tails inside the copy word `(2,1)⌢W^m⌢Z` that follow a `0` or `1` of its `W`s. -/
theorem tailsLe_copies_W_one (Z' : List ℕ) (m j : ℕ) :
    TailsLe 2 ([2,1] ++ copies tW (j + m) ++ ([0,1,2,0] ++ Z')) (copies tW m)
      ([0,1,2,0] ++ Z') := by
  induction m generalizing j with
  | zero => simp [copies, TailsLe]
  | succ m ih =>
    rw [copies_succ, tailsLe_append]
    refine ⟨?_, by rw [show j + (m+1) = (j+1) + m by omega]; exact ih (j+1)⟩
    simp only [tW, TailsLe, List.cons_append, List.nil_append]
    refine ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide), fun _ => ?_, by omega, fun _ => ?_,
      trivial⟩
    · rw [show j + (m+1) = m + (j+1) by omega, copies_add]
      simp only [List.append_assoc]
      apply cons_le_cons_same; apply cons_le_cons_same
      apply append_le_append_left
      rw [copies_succ]
      simp only [List.cons_append, List.nil_append]
      exact (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl,
        List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)⟩)⟩)).le
    · obtain ⟨Z'', hZ''⟩ := copies_W_head m ([0,1,2,0] ++ Z') ⟨[1,2,0] ++ Z', rfl⟩
      simp only [tW, List.cons_append, List.nil_append] at hZ''
      rw [hZ'']
      exact cons_le_of_lt _ _ _ _ (by decide)

theorem tailsLe_tA_end (k : ℕ) (N : List ℕ) : TailsLe 2 (2 :: 1 :: N) (tA k) [] := by
  have hc : ∀ k', TailsLe 2 (2 :: 1 :: N) (copies [0,2] k') [] := by
    intro k'
    induction k' with
    | zero => simp [copies, TailsLe]
    | succ k' ih =>
      rw [copies_succ, tailsLe_append]
      refine ⟨?_, ih⟩
      simp only [TailsLe, List.cons_append, List.nil_append, List.append_nil]
      refine ⟨fun _ => cons_le_cons_same 2 _ _ ?_, by omega, trivial⟩
      cases k' with
      | zero => exact nil_le_list _
      | succ k' => rw [copies_succ]; exact cons_le_of_lt _ _ _ _ (by decide)
  unfold tA
  rw [tailsLe_append]
  refine ⟨?_, hc k⟩
  simp only [TailsLe, List.cons_append, List.nil_append, List.append_nil]
  refine ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide), fun _ => cons_le_cons_same 2 _ _ ?_,
    by omega, trivial⟩
  cases k with
  | zero => exact nil_le_list _
  | succ k => rw [copies_succ]; exact cons_le_of_lt _ _ _ _ (by decide)

/-- The tails of the copy word `N = (2,1)⌢W^m⌢T⌢A_(k+1)` after its own `0`s and `1`s are at
most `N`, given the condition `hT2` on `T`. -/
theorem tailsLe_copy_word (T : List ℕ) (k m : ℕ) (Z' N : List ℕ)
    (hN : N = [2,1] ++ copies tW m ++ T ++ tA (k+1))
    (hT3 : T ++ tA (k+1) = [0,1,2,0] ++ Z') (hT2 : TailsLe 2 N T (tA (k+1))) :
    TailsLe 2 N N [] := by
  have hA : N = [2,1] ++ (copies tW m ++ (T ++ tA (k+1))) := by rw [hN]; simp
  have hN21 : N = 2 :: 1 :: (copies tW m ++ T ++ tA (k+1)) := by rw [hN]; simp
  have P1 : TailsLe 2 N [2,1] (copies tW m ++ (T ++ tA (k+1))) := by
    simp only [TailsLe, List.cons_append, List.nil_append]
    refine ⟨by omega, fun _ => ?_, trivial⟩
    obtain ⟨Z'', hZ''⟩ := copies_W_head m (T ++ tA (k+1)) ⟨[1,2,0] ++ Z', by rw [hT3]; rfl⟩
    rw [hZ'', hN21]
    exact cons_le_of_lt _ _ _ _ (by decide)
  have P2 : TailsLe 2 N (copies tW m) (T ++ tA (k+1)) := by
    have h := tailsLe_copies_W_one Z' m 0
    rw [Nat.zero_add] at h
    rw [hT3, hN, List.append_assoc _ T, hT3]
    exact h
  have P4 : TailsLe 2 N (tA (k+1)) [] := by
    rw [hN21]; exact tailsLe_tA_end (k+1) _
  have h34 : TailsLe 2 N (T ++ tA (k+1)) [] :=
    (tailsLe_append _ _ _ _ _).mpr ⟨by rw [List.append_nil]; exact hT2, P4⟩
  have h234 : TailsLe 2 N (copies tW m ++ (T ++ tA (k+1))) [] :=
    (tailsLe_append _ _ _ _ _).mpr ⟨by rw [List.append_nil]; exact P2, h34⟩
  have h1234 : TailsLe 2 N ([2,1] ++ (copies tW m ++ (T ++ tA (k+1)))) [] :=
    (tailsLe_append _ _ _ _ _).mpr ⟨by rw [List.append_nil]; exact P1, h234⟩
  rw [← hA] at h1234
  exact h1234

theorem breakAt_of_low (S : Sequence) (i j : ℕ) (hpj : p S i < j) (hj : j ≤ fbp S i)
    (he : entry S j ≤ entry S (p S i)) : breakAt S i :=
  Or.inr ⟨j, List.mem_range.mpr (by omega), hpj, he⟩

theorem geAll_copies_02_gen (N' : List ℕ) (j : ℕ) (B : List ℕ) :
    GeAll (0 :: 1 :: N') (copies [0,2] j) B := by
  induction j generalizing B with
  | zero => simp [copies, GeAll]
  | succ j ih =>
    rw [copies_succ, geAll_append]
    refine ⟨?_, ih B⟩
    simp only [GeAll, List.cons_append, List.nil_append]
    exact ⟨(List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)).le,
      cons_le_of_lt _ _ _ _ (by decide), trivial⟩

/-- Every suffix inside a run of `W` beats a word that starts with `(0,1,2,0)`. -/
theorem geAll_copies_W_gen (N' : List ℕ) (j : ℕ) (B : List ℕ) :
    GeAll (0 :: 1 :: 2 :: 0 :: N') (copies tW j) B := by
  induction j generalizing B with
  | zero => simp [copies, GeAll]
  | succ j ih =>
    rw [copies_succ, geAll_append]
    refine ⟨?_, ih B⟩
    simp only [tW, GeAll, List.cons_append, List.nil_append]
    refine ⟨?_, cons_le_of_lt _ _ _ _ (by decide), cons_le_of_lt _ _ _ _ (by decide),
      cons_le_of_lt _ _ _ _ (by decide), trivial⟩
    exact (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl,
      List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)⟩)⟩)).le

theorem copies_02_head (j : ℕ) (B : List ℕ) : ∃ B', copies [0,2] j ++ (0 :: B) = 0 :: B' := by
  cases j with
  | zero => exact ⟨B, by simp [copies]⟩
  | succ j => exact ⟨2 :: (copies [0,2] j ++ 0 :: B), by simp [copies_succ]⟩

/-- The zeros of `(0,2)^j` followed by a `0` have tails `(2,0,…)`, below `(2,1,…)`. -/
theorem tailsLe_copies_02_mid (N' : List ℕ) (j : ℕ) (B : List ℕ) :
    TailsLe 2 (2 :: 1 :: N') (copies [0,2] j) (0 :: B) := by
  induction j with
  | zero => simp [copies, TailsLe]
  | succ j ih =>
    rw [copies_succ, tailsLe_append]
    refine ⟨?_, ih⟩
    simp only [TailsLe, List.cons_append, List.nil_append]
    refine ⟨fun _ => ?_, by omega, trivial⟩
    obtain ⟨B', hB'⟩ := copies_02_head j B
    rw [hB']
    exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩) |>.le

theorem tA_succ (k : ℕ) : tA (k+1) = tA k ++ [0,2] := by
  simp [tA, copies_succ']

/-- L_A, stage 3 at the last unit `A_d W^(m+1)` with `d ≤ k`, followed by `T`:
`R0⌢A_d⌢W^(m+1)⌢T⌢A_(k+1) [n] = R0⌢A_d⌢(W^(m+1)⌢T⌢A_k)^n⌢(0,1)`.
The conditions `hT1`–`hT3` on `T` are the suffix comparisons that place `p 3` at the head of
`A_d` and the record at the `1` of the first `W`. -/
theorem law_A (R0 T Z' : List ℕ) (d k m : ℕ) (hd : d ≤ k)
    (hT3 : T ++ tA (k+1) = [0,1,2,0] ++ Z')
    (hT1 : GeAll (tA (k+1)) T (tA (k+1)))
    (hT2 : TailsLe 2 ([2,1] ++ copies tW m ++ T ++ tA (k+1)) T (tA (k+1))) :
    let S := R0 ++ tA d ++ copies tW (m+1) ++ T ++ tA (k+1)
    p S 3 = R0.length + 1 ∧ br S = 3 ∧ cut S = R0.length + 2 * d + 5 ∧
    ∀ n, fs S n = R0 ++ tA d ++ copies (copies tW (m+1) ++ T ++ tA k) n ++ [0,1] := by
  intro S
  set X := R0 ++ tA d ++ copies tW (m+1) ++ T with hX
  have hSX : S = X ++ tA (k+1) := rfl
  obtain ⟨hp2, -, hnb2⟩ := stage2_A X k
  rw [← hSX] at hp2 hnb2
  have hXl : X.length = R0.length + 2 * d + 4 * m + 7 + T.length := by
    simp [X, tA, copies_length, tW]; omega
  set N := [2,1] ++ copies tW m ++ T ++ tA (k+1) with hN
  have hh : entry S S.length = 2 :=
    entry_last S (X ++ tA k ++ [0]) 2 (by rw [hSX, tA_succ]; simp)
  have hp3 : p S 3 = R0.length + 1 := by
    rw [p_succ, hp2]
    obtain ⟨e, he⟩ : ∃ e, k + 1 = d + (e + 1) := ⟨k - d, by omega⟩
    refine sp_dec S R0 ([1,2] ++ copies [0,2] d ++ copies tW (m+1) ++ T) (tA (k+1)) 0 _ _
      (by simp [S, tA]) (by simp [copies_length, tW] at hXl ⊢; omega) rfl ?_ ?_
    · have h1 : (0 :: ([1,2] ++ copies [0,2] d ++ copies tW (m+1) ++ T ++ tA (k+1))) =
          ([0,1,2] ++ copies [0,2] d) ++ (copies tW (m+1) ++ (T ++ tA (k+1))) := by simp
      have h2 : tA (k+1) = ([0,1,2] ++ copies [0,2] d) ++ copies [0,2] (e+1) := by
        rw [tA, he, copies_add, List.append_assoc]
      rw [h1]
      conv_rhs => rw [h2]
      apply append_lt_append_left
      rw [copies_succ, copies_succ]
      simp only [tW, List.cons_append, List.nil_append]
      exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)
    · rw [geAll_append, geAll_append, geAll_append]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hT1⟩
      · simp only [tA, GeAll, List.cons_append, List.nil_append]
        exact ⟨cons_le_of_lt _ _ _ _ (by decide), cons_le_of_lt _ _ _ _ (by decide), trivial⟩
      · simpa [tA] using geAll_copies_02_gen (2 :: copies [0,2] (k+1)) d
          (copies tW (m+1) ++ (T ++ tA (k+1)))
      · have h := geAll_copies_W_gen (2 :: copies [0,2] k) (m+1) (T ++ tA (k+1))
        rw [show (0 :: 1 :: 2 :: 0 :: 2 :: copies [0,2] k) = tA (k+1) by simp [tA, copies_succ]]
          at h
        exact h
  have hm3 : mbp S (R0.length + 1) = R0.length + 2 * d + 5 := by
    refine mbp_dec S R0 (tA d ++ [0]) N 1 2 _ _ ?_ rfl (by simp [tA, copies_length]; omega)
      (by simp [N]) hh (by decide) ?_
    · simp [S, N, copies_succ, tW]
    · have hN21 : N = 2 :: 1 :: (copies tW m ++ T ++ tA (k+1)) := by simp [N]
      have hself := tailsLe_copy_word T k m Z' N hN hT3 hT2
      rw [tailsLe_append, tailsLe_append]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · unfold tA
        rw [tailsLe_append]
        refine ⟨?_, ?_⟩
        · simp only [TailsLe, List.cons_append, List.nil_append]
          have key : ∀ B N', 2 :: (copies [0,2] d ++ 0 :: B) ≤ 2 :: 1 :: N' := by
            intro B N'
            obtain ⟨B', hB'⟩ := copies_02_head d B
            rw [hB']
            exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩) |>.le
          refine ⟨fun _ => le_of_le_of_eq (cons_le_of_lt _ _ _ _ (by decide)) hN21.symm,
            fun _ => le_of_le_of_eq (key _ _) hN21.symm, by omega, trivial⟩
        · have h := tailsLe_copies_02_mid (copies tW m ++ T ++ tA (k+1)) d (1 :: N)
          rw [← hN21] at h
          simpa using h
      · simp only [TailsLe, List.nil_append, List.append_nil]
        exact ⟨fun _ => le_of_le_of_eq (cons_le_of_lt _ _ _ _ (by decide)) hN21.symm, trivial⟩
      · simp only [TailsLe]
        exact ⟨fun _ => by simp, hself⟩
  have hf3 : fbp S 3 = R0.length + 2 * d + 5 := by simp only [fbp, hp3, hm3]
  have he0 : entry S (R0.length + 2 * d + 4) = 0 :=
    entry_at S (R0 ++ tA d) (copies tW (m+1) ++ T ++ tA (k+1)) 0 _ (by simp [S])
      (by simp [tA, copies_length]; omega) (by simp [copies_succ, tW])
  have he1 : entry S (R0.length + 1) = 0 :=
    entry_at S R0 (tA d ++ copies tW (m+1) ++ T ++ tA (k+1)) 0 _ (by simp [S]) rfl
      (by simp [tA])
  have hL : 3 ≤ S.length := by simp [S, tA]; omega
  have hbr : br S = 3 := br_eq_three S hL hnb2
    (breakAt_of_low S 3 (R0.length + 2 * d + 4) (by omega) (by omega) (by rw [hp3, he0, he1]))
  have hc : cut S = R0.length + 2 * d + 5 := by rw [cut, hbr, hf3]
  refine ⟨hp3, hbr, hc, fun n => ?_⟩
  have hS2 : S = (R0 ++ tA d ++ [0,1]) ++ ([2,1] ++ copies tW m ++ T ++ tA k ++ [0]) ++ [2] := by
    simp [S, tA_succ, copies_succ, tW]
  rw [fs_of_cut_word S _ _ 2 hS2 (by decide) (by rw [hc]; simp [tA, copies_length]; omega) n]
  have h := copies_rotate ([2,1] ++ copies tW m ++ T ++ tA k) [0,1] n
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h ⊢
  rw [h]
  simp [copies_succ, tW]

/-- L_A when no unit `A_d W^(m+1)` with `d ≤ k` precedes: the leading run `W^j` after
`(0,0,2,1)`. Here `p 3 = 1` and the cut is `2`:
`(0,0,2,1)⌢W^j⌢T⌢A_(k+1) [n+1] = (0,0,2,1)⌢W^j⌢T⌢A_k⌢(W^(j+1)⌢T⌢A_k)^n⌢(0,1)`. -/
theorem law_A_lead (T Z' : List ℕ) (j k : ℕ)
    (hT3 : T ++ tA (k+1) = [0,1,2,0] ++ Z')
    (hT1 : GeAll (tA (k+1)) T (tA (k+1)))
    (hT2 : TailsLe 2 ([2,1] ++ copies tW j ++ T ++ tA (k+1)) T (tA (k+1))) :
    let S := [0,0,2,1] ++ copies tW j ++ T ++ tA (k+1)
    p S 3 = 1 ∧ br S = 3 ∧ cut S = 2 ∧
    ∀ n, fs S (n+1) = [0,0,2,1] ++ copies tW j ++ T ++ tA k ++
      copies (copies tW (j+1) ++ T ++ tA k) n ++ [0,1] := by
  intro S
  set X := [0,0,2,1] ++ copies tW j ++ T with hX
  have hSX : S = X ++ tA (k+1) := rfl
  obtain ⟨hp2, -, hnb2⟩ := stage2_A X k
  rw [← hSX] at hp2 hnb2
  set N := [2,1] ++ copies tW j ++ T ++ tA (k+1) with hN
  have hh : entry S S.length = 2 :=
    entry_last S (X ++ tA k ++ [0]) 2 (by rw [hSX, tA_succ]; simp)
  have hp3 : p S 3 = 1 := by
    rw [p_succ, hp2]
    refine sp_dec S [] ([0,2,1] ++ copies tW j ++ T) (tA (k+1)) 0 _ _
      (by simp [S]) (by simp [X]) rfl ?_ ?_
    · simp only [tA, List.cons_append, List.nil_append, List.append_assoc]
      exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)
    · rw [geAll_append, geAll_append]
      refine ⟨⟨?_, ?_⟩, hT1⟩
      · simp only [tA, GeAll, List.cons_append, List.nil_append]
        exact ⟨List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩) |>.le,
          cons_le_of_lt _ _ _ _ (by decide), cons_le_of_lt _ _ _ _ (by decide), trivial⟩
      · have h := geAll_copies_W_gen (2 :: copies [0,2] k) j (T ++ tA (k+1))
        rw [show (0 :: 1 :: 2 :: 0 :: 2 :: copies [0,2] k) = tA (k+1) by simp [tA, copies_succ]]
          at h
        exact h
  have hm3 : mbp S 1 = 2 := by
    refine mbp_dec S [] [0] N 0 2 _ _ (by simp [S, N]) rfl rfl (by simp [N]) hh (by decide) ?_
    have hself := tailsLe_copy_word T k j Z' N hN hT3 hT2
    have hN21 : N = 2 :: 1 :: (copies tW j ++ T ++ tA (k+1)) := by simp [N]
    simp only [TailsLe, List.cons_append, List.nil_append, List.append_nil]
    exact ⟨fun _ => by rw [hN21]; exact cons_le_of_lt _ _ _ _ (by decide), fun _ => le_rfl, hself⟩
  have hf3 : fbp S 3 = 2 := by simp only [fbp, hp3, hm3]
  have he2 : entry S 2 = 0 := by simp [S, entry]
  have he1 : entry S 1 = 0 := by simp [S, entry]
  have hL : 3 ≤ S.length := by simp [S, tA]
  have hbr : br S = 3 := br_eq_three S hL hnb2
    (breakAt_of_low S 3 2 (by omega) (by omega) (by rw [hp3, he2, he1]))
  have hc : cut S = 2 := by rw [cut, hbr, hf3]
  refine ⟨hp3, hbr, hc, fun n => ?_⟩
  have hS2 : S = [0,0] ++ ([2,1] ++ copies tW j ++ T ++ tA k ++ [0]) ++ [2] := by
    simp [S, tA_succ]
  rw [fs_of_cut_word S _ _ 2 hS2 (by decide) (by rw [hc]; rfl) (n+1), copies_succ]
  have h := copies_rotate ([2,1] ++ copies tW j ++ T ++ tA k) [0,1] n
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h ⊢
  rw [h]
  simp [hX, copies_succ, tW]

/-- L_A with `T` empty: `R0⌢A_d⌢W^(m+1)⌢A_(k+1) [n] = R0⌢A_d⌢(W^(m+1)⌢A_k)^n⌢(0,1)`, `d ≤ k`. -/
theorem law_A_adjacent (R0 : List ℕ) (d k m : ℕ) (hd : d ≤ k) :
    let S := R0 ++ tA d ++ copies tW (m+1) ++ tA (k+1)
    br S = 3 ∧ cut S = R0.length + 2 * d + 5 ∧
    ∀ n, fs S n = R0 ++ tA d ++ copies (copies tW (m+1) ++ tA k) n ++ [0,1] := by
  have h := law_A R0 [] (2 :: copies [0,2] k) d k m hd (by simp [tA, copies_succ])
    (by simp [GeAll]) (by simp [TailsLe])
  simp only [List.append_nil] at h
  exact h.2

/-- L_A with `T` empty after the leading run: `(0,0,2,1)⌢W^j⌢A_(k+1) [n+1] =
(0,0,2,1)⌢W^j⌢A_k⌢(W^(j+1)⌢A_k)^n⌢(0,1)`. -/
theorem law_A_lead_adjacent (j k : ℕ) :
    let S := [0,0,2,1] ++ copies tW j ++ tA (k+1)
    br S = 3 ∧ cut S = 2 ∧
    ∀ n, fs S (n+1) = [0,0,2,1] ++ copies tW j ++ tA k ++ copies (copies tW (j+1) ++ tA k) n ++
      [0,1] := by
  have h := law_A_lead [] (2 :: copies [0,2] k) j k (by simp [tA, copies_succ])
    (by simp [GeAll]) (by simp [TailsLe])
  simp only [List.append_nil] at h
  exact h.2

/-! ## L_A with a token string `T`

The conditions of `law_A` on `T` follow from two token-level conditions:
`MidOK K T` (every `A_e` in `T` has `e ≥ K`, and `T` does not start with `W`) and
`BlockLe U K T` (after each `W` or `E` of `T`, the rest followed by `A_K` is at most `U`).
`BlockLe` compares the `(2,1)`-blocks: the block of the copy word against the blocks that
start at the last `(2,1)` of each later `W` or `E`. -/

inductive Tok
  | A (e : ℕ)
  | E
  | W
  deriving DecidableEq

def Tok.raw : Tok → List ℕ
  | .A e => tA e
  | .E => tE
  | .W => tW

def rawT (T : List Tok) : List ℕ := (T.map Tok.raw).flatten

@[simp] theorem rawT_nil : rawT [] = [] := rfl
@[simp] theorem rawT_cons (t : Tok) (T : List Tok) : rawT (t :: T) = t.raw ++ rawT T := by
  simp [rawT]

def MidOK (K : ℕ) (T : List Tok) : Prop :=
  (∀ e, Tok.A e ∈ T → K ≤ e) ∧ T.head? ≠ some Tok.W

def BlockLe (U : List ℕ) (K : ℕ) : List Tok → Prop
  | [] => True
  | t :: T => ((t = .W ∨ t = .E) → rawT T ++ tA K ≤ U) ∧ BlockLe U K T

theorem tA_add (K j : ℕ) : tA (K + j) = tA K ++ copies [0,2] j := by
  simp [tA, copies_add]

theorem rawT_tA_head (T : List Tok) (K : ℕ) : ∃ B, rawT T ++ tA K = 0 :: B := by
  cases T with
  | nil => exact ⟨[1,2] ++ copies [0,2] K, by simp [tA]⟩
  | cons t T =>
    cases t with
    | A e => exact ⟨[1,2] ++ copies [0,2] e ++ rawT T ++ tA K, by simp [Tok.raw, tA]⟩
    | E => exact ⟨[1,2,0,2,1] ++ rawT T ++ tA K, by simp [Tok.raw, tE]⟩
    | W => exact ⟨[1,2,1] ++ rawT T ++ tA K, by simp [Tok.raw, tW]⟩

/-- Suffixes inside a token `A_e`, `E` or `W` are at least `A_K` when `1 ≤ K ≤ e`. -/
theorem geAll_tok (k : ℕ) (t : Tok) (ht : ∀ e, t = .A e → k+1 ≤ e) (B : List ℕ) :
    GeAll (tA (k+1)) t.raw B := by
  have hK : tA (k+1) = 0 :: 1 :: (2 :: copies [0,2] (k+1)) := by simp [tA]
  cases t with
  | A e =>
    obtain ⟨j, rfl⟩ : ∃ j, e = (k+1) + j := ⟨e - (k+1), by have := ht e rfl; omega⟩
    have hr : (Tok.A (k+1+j)).raw = [0,1,2] ++ copies [0,2] (k+1+j) := rfl
    rw [hr, geAll_append]
    refine ⟨?_, by rw [hK]; exact geAll_copies_02_gen _ _ _⟩
    simp only [GeAll, List.cons_append, List.nil_append]
    refine ⟨?_, by rw [hK]; exact cons_le_of_lt _ _ _ _ (by decide),
      by rw [hK]; exact cons_le_of_lt _ _ _ _ (by decide), trivial⟩
    have h := lex_le_append (tA (k+1)) (copies [0,2] j ++ B)
    rw [copies_add]
    simpa [tA, List.append_assoc] using h
  | E =>
    simp only [Tok.raw, tE, GeAll, List.cons_append, List.nil_append]
    refine ⟨?_, by rw [hK]; exact cons_le_of_lt _ _ _ _ (by decide),
      by rw [hK]; exact cons_le_of_lt _ _ _ _ (by decide), ?_,
      by rw [hK]; exact cons_le_of_lt _ _ _ _ (by decide),
      by rw [hK]; exact cons_le_of_lt _ _ _ _ (by decide), trivial⟩
    · cases k with
      | zero => simpa [tA, copies] using lex_le_append [0,1,2,0,2] (1 :: B)
      | succ k =>
        simp only [tA, copies_succ, List.cons_append, List.nil_append]
        exact (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl,
          List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl,
          List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)⟩)⟩)⟩)⟩)).le
    · rw [hK]
      exact (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)).le
  | W =>
    simp only [Tok.raw, tW, GeAll, List.cons_append, List.nil_append]
    refine ⟨?_, by rw [hK]; exact cons_le_of_lt _ _ _ _ (by decide),
      by rw [hK]; exact cons_le_of_lt _ _ _ _ (by decide),
      by rw [hK]; exact cons_le_of_lt _ _ _ _ (by decide), trivial⟩
    rw [hK]
    exact (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl,
      List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)⟩)⟩)).le

theorem midOK_hT1 (k : ℕ) (T : List Tok) (hT : ∀ e, Tok.A e ∈ T → k+1 ≤ e) (B : List ℕ) :
    GeAll (tA (k+1)) (rawT T) B := by
  induction T generalizing B with
  | nil => simp [GeAll]
  | cons t T ih =>
    rw [rawT_cons, geAll_append]
    exact ⟨geAll_tok k t (fun e he => hT e (by simp [he])) _,
      ih (fun e he => hT e (by simp [he])) B⟩

theorem midOK_hT3 (k : ℕ) (T : List Tok) (hT : MidOK (k+1) T) :
    ∃ Z', rawT T ++ tA (k+1) = [0,1,2,0] ++ Z' := by
  cases T with
  | nil => exact ⟨[2] ++ copies [0,2] k, by simp [tA, copies_succ]⟩
  | cons t T =>
    cases t with
    | A e =>
      obtain ⟨j, rfl⟩ : ∃ j, e = (k+1) + j := ⟨e - (k+1), by have := hT.1 e (by simp); omega⟩
      exact ⟨[2] ++ copies [0,2] (k+j) ++ rawT T ++ tA (k+1), by
        simp [Tok.raw, tA, show k + 1 + j = (k + j) + 1 by omega, copies_succ]⟩
    | E => exact ⟨[2,1] ++ rawT T ++ tA (k+1), by simp [Tok.raw, tE]⟩
    | W => exact absurd rfl hT.2

/-- The tails after the `0`s and `1`s of the tokens of `T` are at most the copy word
`(2,1)⌢U`, given the block order. -/
theorem blockLe_hT2 (k : ℕ) (U : List ℕ) (T : List Tok) (hT : ∀ e, Tok.A e ∈ T → k+1 ≤ e)
    (hB : BlockLe U (k+1) T) : TailsLe 2 (2 :: 1 :: U) (rawT T) (tA (k+1)) := by
  induction T with
  | nil => simp [TailsLe]
  | cons t T ih =>
    rw [rawT_cons, tailsLe_append]
    refine ⟨?_, ih (fun e he => hT e (by simp [he])) hB.2⟩
    obtain ⟨B, hB0⟩ := rawT_tA_head T (k+1)
    have hblk := hB.1
    rw [hB0] at hblk ⊢
    cases t with
    | A e =>
      have he : k+1 ≤ e := hT e (by simp)
      obtain ⟨j, rfl⟩ : ∃ j, e = j + 1 := ⟨e - 1, by omega⟩
      simp only [Tok.raw, tA]
      rw [tailsLe_append]
      refine ⟨?_, tailsLe_copies_02_mid _ _ _⟩
      simp only [TailsLe, List.cons_append, List.nil_append]
      refine ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide), fun _ => ?_, by omega, trivial⟩
      rw [copies_succ]
      exact (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)).le
    | E =>
      simp only [Tok.raw, tE, TailsLe, List.cons_append, List.nil_append]
      refine ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide),
        fun _ => (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, cons_lt_of_lt _ _ _ _ (by decide)⟩)).le,
        by omega, fun _ => ?_, by omega, fun _ => cons_le_of_lt _ _ _ _ (by decide), trivial⟩
      exact cons_le_cons_same 2 _ _ (cons_le_cons_same 1 _ _ (hblk (Or.inr rfl)))
    | W =>
      simp only [Tok.raw, tW, TailsLe, List.cons_append, List.nil_append]
      refine ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide), fun _ => ?_, by omega,
        fun _ => cons_le_of_lt _ _ _ _ (by decide), trivial⟩
      exact cons_le_cons_same 2 _ _ (cons_le_cons_same 1 _ _ (hblk (Or.inl rfl)))

/-- L_A for a token string `T`: `R0⌢A_d⌢W^(m+1)⌢T⌢A_(k+1) [n] = R0⌢A_d⌢(W^(m+1)⌢T⌢A_k)^n⌢(0,1)`
when `d ≤ k`, every `A_e` in `T` has `e ≥ k+1`, `T` does not start with `W`, and the
`(2,1)`-blocks after the `W`s and `E`s of `T` are at most `W^m⌢T⌢A_(k+1)`. -/
theorem law_A_tok (R0 : List ℕ) (T : List Tok) (d k m : ℕ) (hd : d ≤ k)
    (hT : MidOK (k+1) T) (hB : BlockLe (copies tW m ++ rawT T ++ tA (k+1)) (k+1) T) :
    let S := R0 ++ tA d ++ copies tW (m+1) ++ rawT T ++ tA (k+1)
    p S 3 = R0.length + 1 ∧ br S = 3 ∧ cut S = R0.length + 2 * d + 5 ∧
    ∀ n, fs S n = R0 ++ tA d ++ copies (copies tW (m+1) ++ rawT T ++ tA k) n ++ [0,1] := by
  obtain ⟨Z', hZ'⟩ := midOK_hT3 k T hT
  have h2 := blockLe_hT2 k _ T hT.1 hB
  exact law_A R0 (rawT T) Z' d k m hd hZ' (midOK_hT1 k T hT.1 _) (by simpa using h2)

/-- L_A for a token string `T` after the leading run `W^j`. -/
theorem law_A_lead_tok (T : List Tok) (j k : ℕ)
    (hT : MidOK (k+1) T) (hB : BlockLe (copies tW j ++ rawT T ++ tA (k+1)) (k+1) T) :
    let S := [0,0,2,1] ++ copies tW j ++ rawT T ++ tA (k+1)
    p S 3 = 1 ∧ br S = 3 ∧ cut S = 2 ∧
    ∀ n, fs S (n+1) = [0,0,2,1] ++ copies tW j ++ rawT T ++ tA k ++
      copies (copies tW (j+1) ++ rawT T ++ tA k) n ++ [0,1] := by
  obtain ⟨Z', hZ'⟩ := midOK_hT3 k T hT
  have h2 := blockLe_hT2 k _ T hT.1 hB
  exact law_A_lead (rawT T) Z' j k hZ' (midOK_hT1 k T hT.1 _) (by simpa using h2)

end SSOS.Seq
