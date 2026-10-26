import SSOS.TokenCut

/-!
Prefix-shift lemmas for the fundamental sequence after a complete `A0` unit.
The generic certificate proves that a cut shifts with an arbitrary prefix when the
parent searches up to the first break have strict predecessors inside the word.
The token-language proof of that certificate is separate from these search lemmas.
-/

namespace SSOS.Seq

/-- Tokens for the prefix lemma; `D` is deliberately local to this file. -/
inductive PrefixTok
  | A (k : ℕ) | W | E | D
  deriving DecidableEq

def PrefixTok.raw : PrefixTok → List ℕ
  | .A k => tA k
  | .W => tW
  | .E => tE
  | .D => [0,2]

def PrefixTok.rawWord (w : List PrefixTok) : List ℕ := (w.map PrefixTok.raw).flatten

/-- Every zero has its complete `01 2` or `02` continuation. -/
inductive ZeroSafe : List ℕ → Prop
  | nil : ZeroSafe []
  | one {s} : ZeroSafe s → ZeroSafe (1 :: s)
  | two {s} : ZeroSafe s → ZeroSafe (2 :: s)
  | zero12 {s} : ZeroSafe s → ZeroSafe (0 :: 1 :: 2 :: s)
  | zero2 {s} : ZeroSafe s → ZeroSafe (0 :: 2 :: s)

theorem zeroSafe_append {s t : List ℕ} (hs : ZeroSafe s) (ht : ZeroSafe t) :
    ZeroSafe (s ++ t) := by
  induction hs with
  | nil => simpa using ht
  | one _ ih => simpa using ZeroSafe.one ih
  | two _ ih => simpa using ZeroSafe.two ih
  | zero12 _ ih => simpa using ZeroSafe.zero12 ih
  | zero2 _ ih => simpa using ZeroSafe.zero2 ih

theorem zeroSafe_D_copies (k : ℕ) : ZeroSafe (copies [0,2] k) := by
  induction k with
  | zero => simpa [copies] using ZeroSafe.nil
  | succ k ih => simpa [copies_succ] using ZeroSafe.zero2 ih

theorem zeroSafe_token (t : PrefixTok) : ZeroSafe t.raw := by
  cases t with
  | D => exact ZeroSafe.zero2 ZeroSafe.nil
  | W => exact ZeroSafe.zero12 (ZeroSafe.one ZeroSafe.nil)
  | E => exact ZeroSafe.zero12 (ZeroSafe.zero2 (ZeroSafe.one ZeroSafe.nil))
  | A k => exact ZeroSafe.zero12 (zeroSafe_D_copies k)

theorem zeroSafe_rawWord (w : List PrefixTok) : ZeroSafe (PrefixTok.rawWord w) := by
  induction w with
  | nil => exact ZeroSafe.nil
  | cons t ts ih =>
      simpa [PrefixTok.rawWord] using zeroSafe_append (zeroSafe_token t) ih

theorem zeroSafe_tail {a : ℕ} {s : List ℕ} (h : ZeroSafe (a :: s)) : ZeroSafe s := by
  cases h with
  | one hs => exact hs
  | two hs => exact hs
  | zero12 hs => exact ZeroSafe.one (ZeroSafe.two hs)
  | zero2 hs => exact ZeroSafe.two hs

theorem zeroSafe_drop {s : List ℕ} (h : ZeroSafe s) (i : ℕ) : ZeroSafe (s.drop i) := by
  induction i generalizing s with
  | zero => simpa using h
  | succ i ih =>
      cases s with
      | nil => exact ZeroSafe.nil
      | cons a s => simpa using ih (zeroSafe_tail h)

theorem zeroSafe_zero_shape {s : List ℕ} (h : ZeroSafe (0 :: s)) :
    (∃ r, s = 1 :: 2 :: r) ∨ (∃ r, s = 2 :: r) := by
  cases h with
  | zero12 hs => exact Or.inl ⟨_, rfl⟩
  | zero2 hs => exact Or.inr ⟨_, rfl⟩

/-- A nonempty safe suffix below a final `02` starts at a complete `012` head. -/
theorem zeroSafe_lt_final_D {s : List ℕ} (h : ZeroSafe s) (hne : s ≠ [])
    (hlt : s < [0,2]) : ∃ r, s = [0,1,2] ++ r := by
  cases h with
  | nil => contradiction
  | one hs => simp [List.cons_lt_cons_iff] at hlt
  | two hs => simp [List.cons_lt_cons_iff] at hlt
  | zero12 hs => exact ⟨_, rfl⟩
  | zero2 hs => simp at hlt

/-- A longer safe suffix below `01202...` also has the fourth, zero entry. -/
theorem zeroSafe_lt_A_succ_shape {s R : List ℕ} (h : ZeroSafe s)
    (hlt : s < [0,1,2,0,2] ++ R)
    (hlen : ([0,1,2,0,2] ++ R).length < s.length) :
    ∃ u, s = [0,1,2,0] ++ u := by
  cases h with
  | nil => simp at hlen
  | one hs => simp [List.cons_lt_cons_iff] at hlt
  | two hs => simp [List.cons_lt_cons_iff] at hlt
  | zero2 hs => simp [List.cons_lt_cons_iff] at hlt
  | zero12 hs =>
      cases hs with
      | nil => simp at hlen; omega
      | one hs => simp [List.cons_lt_cons_iff] at hlt
      | two hs => simp [List.cons_lt_cons_iff] at hlt
      | zero12 hs => exact ⟨_, rfl⟩
      | zero2 hs => exact ⟨_, rfl⟩

theorem zeroSafe_lt_W_head {s : List ℕ} (h : ZeroSafe s) (hne : s ≠ [])
    (hlt : s < tW) : ∃ u, s = 0 :: u := by
  cases h with
  | nil => contradiction
  | one hs => simp [tW, List.cons_lt_cons_iff] at hlt
  | two hs => simp [tW, List.cons_lt_cons_iff] at hlt
  | zero12 hs => exact ⟨_, rfl⟩
  | zero2 hs => simp [tW, List.cons_lt_cons_iff] at hlt

theorem rawWord_append (u v : List PrefixTok) :
    PrefixTok.rawWord (u ++ v) = PrefixTok.rawWord u ++ PrefixTok.rawWord v := by
  simp [PrefixTok.rawWord, List.map_append, List.flatten_append]

theorem rawWord_singleton (t : PrefixTok) : PrefixTok.rawWord [t] = t.raw := by
  simp [PrefixTok.rawWord]

theorem rawWord_replicate_D (r : ℕ) :
    PrefixTok.rawWord (List.replicate r PrefixTok.D) = copies [0,2] r := by
  simp [PrefixTok.rawWord, PrefixTok.raw, copies]

theorem token_raw_starts_zero (t : PrefixTok) : ∃ v, t.raw = 0 :: v := by
  cases t with
  | A k => exact ⟨1 :: 2 :: copies [0,2] k, by simp [PrefixTok.raw, tA]⟩
  | W => exact ⟨[1,2,1], rfl⟩
  | E => exact ⟨[1,2,0,2,1], rfl⟩
  | D => exact ⟨[2], rfl⟩

theorem rawWord_starts_zero (w : List PrefixTok) (hw : w ≠ []) :
    ∃ v, PrefixTok.rawWord w = 0 :: v := by
  cases w with
  | nil => contradiction
  | cons t ts =>
      obtain ⟨v, hv⟩ := token_raw_starts_zero t
      exact ⟨v ++ PrefixTok.rawWord ts, by simp [PrefixTok.rawWord, hv]⟩

theorem rawWord_head_nonD (t : PrefixTok) (w : List PrefixTok) (ht : t ≠ .D) :
    ∃ v, PrefixTok.rawWord (t :: w) = [0,1,2] ++ v := by
  cases t with
  | D => exact False.elim (ht rfl)
  | A k => exact ⟨copies [0,2] k ++ PrefixTok.rawWord w,
      by simp [PrefixTok.rawWord, PrefixTok.raw, tA]⟩
  | W => exact ⟨1 :: PrefixTok.rawWord w, by simp [PrefixTok.rawWord, PrefixTok.raw, tW]⟩
  | E => exact ⟨[0,2,1] ++ PrefixTok.rawWord w,
      by simp [PrefixTok.rawWord, PrefixTok.raw, tE]⟩

/-- Every internal `21` must be followed by zero. -/
def NoBad21 : List ℕ → Prop
  | a :: b :: c :: s => (a = 2 ∧ b = 1 → c = 0) ∧ NoBad21 (b :: c :: s)
  | _ => True
termination_by s => s.length

theorem noBad21_tail {a : ℕ} {s : List ℕ} (h : NoBad21 (a :: s)) : NoBad21 s := by
  cases s with
  | nil => simp [NoBad21]
  | cons b s =>
      cases s with
      | nil => simp [NoBad21]
      | cons c s =>
          simp only [NoBad21] at h
          exact h.2

theorem noBad21_drop {s : List ℕ} (h : NoBad21 s) (i : ℕ) :
    NoBad21 (s.drop i) := by
  induction i generalizing s with
  | zero => simpa using h
  | succ i ih =>
      cases s with
      | nil => trivial
      | cons a s => simpa using ih (noBad21_tail h)

theorem noBad21_append_zero (l r : List ℕ) (hl : NoBad21 l)
    (hr : NoBad21 (0 :: r)) : NoBad21 (l ++ 0 :: r) := by
  induction l with
  | nil => simpa using hr
  | cons a l ih =>
      cases l with
      | nil =>
          cases r with
          | nil => simp [NoBad21]
          | cons c r =>
              simp only [List.cons_append, List.nil_append, NoBad21]
              exact ⟨by omega, hr⟩
      | cons b l =>
          cases l with
          | nil =>
              simp only [List.cons_append, List.nil_append, NoBad21]
              refine ⟨by simp, ?_⟩
              cases r with
              | nil => simp [NoBad21]
              | cons c r =>
                  simp only [NoBad21]
                  exact ⟨by omega, hr⟩
          | cons c l =>
              have hh := hl
              simp only [NoBad21] at hh
              have hhead : a = 2 ∧ b = 1 → c = 0 := hh.1
              have hrest : NoBad21 (b :: c :: l) := hh.2
              simp only [List.cons_append, NoBad21]
              exact ⟨hhead, ih hrest⟩

theorem noBad21_A (k : ℕ) : NoBad21 (tA k) := by
  induction k with
  | zero => simp [NoBad21, tA, copies]
  | succ k ih =>
      rw [tA_succ]
      exact noBad21_append_zero (tA k) [2] ih (by simp [NoBad21])

theorem noBad21_D_copies (k : ℕ) : NoBad21 (copies [0,2] k) := by
  induction k with
  | zero => simp [copies, NoBad21]
  | succ k ih =>
      rw [copies_succ']
      exact noBad21_append_zero (copies [0,2] k) [2] ih (by simp [NoBad21])

theorem noBad21_token (t : PrefixTok) : NoBad21 t.raw := by
  cases t with
  | A k => exact noBad21_A k
  | W => simp [PrefixTok.raw, tW, NoBad21]
  | E => simp [PrefixTok.raw, tE, NoBad21]
  | D => simp [PrefixTok.raw, NoBad21]

theorem noBad21_rawWord (w : List PrefixTok) : NoBad21 (PrefixTok.rawWord w) := by
  induction w with
  | nil => simp [PrefixTok.rawWord, NoBad21]
  | cons t ts ih =>
      by_cases hts : ts = []
      · subst ts
        simpa [PrefixTok.rawWord] using noBad21_token t
      · obtain ⟨r, hraw⟩ := rawWord_starts_zero ts hts
        have h := noBad21_append_zero t.raw r (noBad21_token t) (by simpa [hraw] using ih)
        change NoBad21 (t.raw ++ PrefixTok.rawWord ts)
        rw [hraw]
        exact h

/-- A long suffix below a `W` head either has its fourth zero or its fifth zero. -/
theorem safe_lt_W_shape {s R : List ℕ} (hz : ZeroSafe s) (hb : NoBad21 s)
    (hlt : s < tW ++ R) (hlen : 5 ≤ s.length) :
    (∃ U, s = [0,1,2,0] ++ U) ∨ (∃ U, s = [0,1,2,1,0] ++ U) := by
  cases hz with
  | nil => simp at hlen
  | one hs => simp [tW, List.cons_lt_cons_iff] at hlt
  | two hs => simp [tW, List.cons_lt_cons_iff] at hlt
  | zero2 hs => simp [tW, List.cons_lt_cons_iff] at hlt
  | zero12 hs =>
      cases hs with
      | nil => simp at hlen
      | two hs => simp [tW, List.cons_lt_cons_iff] at hlt
      | zero12 hs => exact Or.inl ⟨_, rfl⟩
      | zero2 hs => exact Or.inl ⟨_, rfl⟩
      | one hs =>
          cases hs with
          | nil => simp at hlen
          | zero12 hs => exact Or.inr ⟨_, rfl⟩
          | zero2 hs => exact Or.inr ⟨_, rfl⟩
          | one hs =>
              have h := noBad21_drop hb 2
              simp [NoBad21] at h
          | two hs =>
              have h := noBad21_drop hb 2
              simp [NoBad21] at h

theorem word_end_decomp (w : List PrefixTok) (hw : w ≠ []) :
    ∃ v t, w = v ++ [t] := by
  induction w with
  | nil => contradiction
  | cons t ts ih =>
      by_cases hts : ts = []
      · subst ts
        exact ⟨[], t, by simp⟩
      · obtain ⟨v, u, hu⟩ := ih hts
        exact ⟨t :: v, u, by simp [hu]⟩

/-- Every word with a non-`D` first token has a last non-`D` token. -/
theorem word_trailing_D_decomp (t : PrefixTok) (w : List PrefixTok)
    (ht : t ≠ .D) :
    ∃ u x r, t :: w = u ++ [x] ++ List.replicate r PrefixTok.D ∧ x ≠ .D := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨[], t, 0, by simp, ht⟩
  | append_singleton w x ih =>
      by_cases hx : x = .D
      · obtain ⟨u, y, r, hdecomp, hy⟩ := ih
        refine ⟨u, y, r+1, ?_, hy⟩
        have h := congrArg (fun z : List PrefixTok => z ++ [.D]) hdecomp
        simpa [hx, List.replicate_succ', List.append_assoc] using h
      · exact ⟨t :: w, x, 0, by simp, hx⟩

theorem token_raw_ends_positive (t : PrefixTok) :
    ∃ u a, t.raw = u ++ [a+1] := by
  cases t with
  | D => exact ⟨[0], 1, rfl⟩
  | W => exact ⟨[0,1,2], 0, rfl⟩
  | E => exact ⟨[0,1,2,0,2], 0, rfl⟩
  | A k =>
      cases k with
      | zero => exact ⟨[0,1], 1, by simp [PrefixTok.raw, tA, copies]⟩
      | succ k =>
          exact ⟨tA k ++ [0], 1, by simp [PrefixTok.raw, tA_succ, List.append_assoc]⟩

theorem rawWord_ends_positive (w : List PrefixTok) (hw : w ≠ []) :
    ∃ u a, PrefixTok.rawWord w = u ++ [a+1] := by
  obtain ⟨v, t, rfl⟩ := word_end_decomp w hw
  obtain ⟨u, a, h⟩ := token_raw_ends_positive t
  exact ⟨PrefixTok.rawWord v ++ u, a, by simp [rawWord_append, rawWord_singleton, h,
    List.append_assoc]⟩

/-- Suffixes at positions inside the appended word ignore the prefix. -/
theorem suf_prefix_shift (Z T : List ℕ) (i : ℕ) (hi : 1 ≤ i) :
    suf (Z ++ T) (Z.length + i) = suf T i := by
  have h := suf_app Z T (i - 1)
  rw [show Z.length + (i - 1) + 1 = Z.length + i by omega] at h
  simpa [suf] using h

theorem suf_shift (S : List ℕ) (i d : ℕ) (hi : 1 ≤ i) :
    suf S (i+d) = (suf S i).drop d := by
  simp [suf, List.drop_drop, show i+d-1 = i-1+d by omega]

theorem entry_of_suf_cons (S : List ℕ) (i a : ℕ) (R : List ℕ)
    (hi : 1 ≤ i) (hiL : i ≤ S.length) (h : suf S i = a :: R) :
    entry S i = a := by
  rw [suf_cons S i hi hiL] at h
  exact (List.cons.inj h).1

/-- Entries at positions inside the appended word ignore the prefix. -/
theorem entry_prefix_shift (Z T : List ℕ) (i : ℕ) (hi : 1 ≤ i) (hiT : i ≤ T.length) :
    entry (Z ++ T) (Z.length + i) = entry T i := by
  have h := entry_app Z T (i - 1) (by omega)
  rw [show Z.length + (i - 1) + 1 = Z.length + i by omega] at h
  rw [h]
  have hidx : i - 1 < T.length := by omega
  simp [entry, List.getElem?_eq_getElem hidx]

theorem candidate_prefix_shift (Z T : List ℕ) (j : ℕ) (hj : 1 ≤ j) (hT : T ≠ []) :
    Candidate (Z ++ T) (Z.length + j) ↔ Candidate T j := by
  have hlen : 1 ≤ T.length := List.length_pos_iff.mpr hT
  have hlast := entry_prefix_shift Z T T.length hlen le_rfl
  constructor
  · rintro ⟨hjL, he⟩
    have hjTL : j < T.length := by simp at hjL; omega
    refine ⟨hjTL, ?_⟩
    rw [show (Z ++ T).length = Z.length + T.length by simp, hlast,
      entry_prefix_shift Z T j hj (by omega)] at he
    exact he
  · rintro ⟨hjL, he⟩
    refine ⟨by simp; omega, ?_⟩
    rw [show (Z ++ T).length = Z.length + T.length by simp, hlast,
      entry_prefix_shift Z T j hj (by omega)]
    exact he

/-- A local strict predecessor makes `sp` independent of every earlier prefix. -/
theorem sp_prefix_shift_of_candidate (Z T : List ℕ) (x a : ℕ)
    (ha : 1 ≤ a) (hax : a < x) (hlt : suf T a < suf T x)
    (hsp : sp T x = a) :
    sp (Z ++ T) (Z.length + x) = Z.length + a := by
  apply sp_eq_of (Z ++ T) (Z.length + x) (Z.length + a)
    (by omega) (by omega)
  · simpa only [suf_prefix_shift Z T a ha, suf_prefix_shift Z T x (by omega)] using hlt
  · intro i hai hix hs
    have hzi : Z.length < i := by omega
    let j := i - Z.length
    have hj : 1 ≤ j := by dsimp [j]; omega
    have hij : i = Z.length + j := by dsimp [j]; omega
    have haj : a < j := by omega
    have hjx : j < x := by omega
    rw [hij, suf_prefix_shift Z T j hj,
      suf_prefix_shift Z T x (by omega)] at hs
    have hbound := ((sp_le_iff T x a).1 (by rw [hsp])).2 j hj hjx hs
    omega

/-- If position one is a strict predecessor, the chosen predecessor is genuine. -/
theorem sp_result_candidate_of_one (T : List ℕ) (x : ℕ) (hx : 1 < x)
    (hone : suf T 1 < suf T x) :
    1 ≤ sp T x ∧ sp T x < x ∧ suf T (sp T x) < suf T x := by
  have hmem := foldl_max_origin
    ((List.range x).filter fun i => 1 ≤ i ∧ suf T i < suf T x) 1
  change sp T x = 1 ∨ sp T x ∈
    ((List.range x).filter fun i => 1 ≤ i ∧ suf T i < suf T x) at hmem
  rcases hmem with h1 | hm
  · rw [h1]
    exact ⟨le_rfl, hx, hone⟩
  · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hm
    exact ⟨hm.2.1, hm.1, hm.2.2⟩

/-- The first parent scan of a word starting in `A0` is always local. -/
theorem first_parent_candidate (U : List ℕ) (a : ℕ) :
    let T := tA 0 ++ U ++ [a+1]
    ∃ r, 1 ≤ r ∧ r < p T 0 ∧ suf T r < suf T (p T 0) ∧
      sp T (p T 0) = r := by
  intro T
  have hL : 1 < T.length := by simp [T, tA, copies]
  have he1 : entry T 1 = 0 := by simp [T, entry, tA, copies]
  have helast : entry T T.length = a+1 :=
    entry_last T (tA 0 ++ U) (a+1) (by simp [T])
  have hone : suf T 1 < suf T T.length := by
    apply (suf_lt_last_iff T 1 (by omega) (by omega)).2
    rw [he1, helast]
    omega
  obtain ⟨hr1, hrL, hlt⟩ := sp_result_candidate_of_one T T.length hL hone
  refine ⟨sp T T.length, ?_, ?_, ?_, rfl⟩
  · simpa [p] using hr1
  · simpa [p] using hrL
  · simpa [p] using hlt

theorem head_lt_parent_zero_word (w : List PrefixTok) (hw : w ≠ []) :
    let T := tA 0 ++ PrefixTok.rawWord w
    1 < p T 0 ∧ suf T 1 < suf T (p T 0) := by
  obtain ⟨u, a, hraw⟩ := rawWord_ends_positive w hw
  let T := tA 0 ++ u ++ [a+1]
  have hL : 1 < T.length := by simp [T, tA, copies]
  have he1 : entry T 1 = 0 := by simp [T, entry, tA, copies]
  have helast : entry T T.length = a+1 :=
    entry_last T (tA 0 ++ u) (a+1) (by simp [T])
  have hs : suf T 1 < suf T T.length := by
    apply (suf_lt_last_iff T 1 (by omega) (by omega)).2
    rw [he1, helast]
    omega
  simpa [T, hraw, p, List.append_assoc] using And.intro hL hs

/-- A final `D` has its last zero as the first parent, after any prefix. -/
theorem p_one_final_D (Y : List ℕ) : p (Y ++ [0,2]) 1 = Y.length + 1 := by
  apply p_one_eq_last (Y ++ [0,2]) (Y.length + 1)
  · omega
  · simp
  · simp [entry]
  · intro i hi hiL
    have : i = Y.length + 2 := by simp at hiL; omega
    subst i
    simp

/-- A complete initial `A0` beats the suffix at the first parent of a final `D`. -/
theorem head_lt_parent_one_final_D (U : List ℕ) :
    let T := tA 0 ++ U ++ [0,2]
    1 < p T 1 ∧ suf T 1 < suf T (p T 1) := by
  intro T
  have hp : p T 1 = (tA 0 ++ U).length + 1 := by
    simpa [T, List.append_assoc] using p_one_final_D (tA 0 ++ U)
  have hs : suf T (p T 1) = [0,2] := by
    rw [hp]
    simpa [T, List.append_assoc] using suf_app (tA 0 ++ U) [0,2] 0
  refine ⟨by rw [hp]; simp [tA, copies], ?_⟩
  rw [hs]
  simp [suf, T, tA, copies, List.cons_lt_cons_iff]

/-- The internal `D` of a final `E` is its first parent. -/
theorem head_lt_parent_one_final_E (U : List ℕ) :
    let T := tA 0 ++ U ++ tE
    1 < p T 1 ∧ suf T 1 < suf T (p T 1) := by
  intro T
  have hp : p T 1 = (tA 0 ++ U).length + 4 := by
    simpa [T, List.append_assoc] using (cut_E (tA 0 ++ U)).1
  have hs : suf T (p T 1) = [0,2,1] := by
    rw [hp]
    simpa [T, tE, List.append_assoc] using suf_app (tA 0 ++ U) tE 3
  refine ⟨by rw [hp]; simp [tA, copies], ?_⟩
  rw [hs]
  simp [suf, T, tA, tE, copies, List.cons_lt_cons_iff]

theorem head_lt_parent_one_final_A0 (U : List ℕ) :
    let T := tA 0 ++ U ++ tA 0
    1 < p T 1 ∧ suf T 1 < suf T (p T 1) := by
  intro T
  have hp : p T 1 = (tA 0 ++ U).length + 2 := by
    simpa [T, tA, copies, List.append_assoc] using (cut_A0 (tA 0 ++ U)).1
  have hs : suf T (p T 1) = [1,2] := by
    rw [hp]
    simpa [T, tA, copies, List.append_assoc] using
      suf_app (tA 0 ++ U) (tA 0) 1
  refine ⟨by rw [hp]; simp [tA, copies], ?_⟩
  rw [hs]
  simp [suf, T, tA, copies, List.cons_lt_cons_iff]

theorem head_lt_parent_one_final_A_succ (U : List ℕ) (k : ℕ) :
    let T := tA 0 ++ U ++ tA (k+1)
    1 < p T 1 ∧ suf T 1 < suf T (p T 1) := by
  simpa [tA_succ, List.append_assoc] using
    head_lt_parent_one_final_D (U ++ tA k)

theorem p_one_final_W (Y : List ℕ) : p (Y ++ tW) 1 = Y.length + 1 := by
  apply p_one_eq_last (Y ++ tW) (Y.length + 1)
  · omega
  · simp [tW]
  · simp [entry, tW]
  · intro i hi hiL
    have hi' : i = Y.length + 2 ∨ i = Y.length + 3 := by simp [tW] at hiL; omega
    rcases hi' with h | h
    · subst i
      rw [entry_app Y tW 1 (by simp [tW])]
      simp [entry, tW]
    · subst i
      rw [entry_app Y tW 2 (by simp [tW])]
      simp [entry, tW]

/-- Stage two of a final `W D^(m+1)` points to the head of that `W`. -/
theorem p_two_final_W_D_run (Y : List ℕ) (m : ℕ) :
    p (Y ++ tW ++ copies [0,2] (m+1)) 2 = Y.length + 1 := by
  let S := Y ++ tW ++ copies [0,2] (m+1)
  have hp1 : p S 1 = Y.length + 4 + 2*m + 1 := by
    have h := p_one_final_D (Y ++ tW ++ copies [0,2] m)
    have h' : p S 1 = (Y ++ tW ++ copies [0,2] m).length + 1 := by
      simpa [S, copies_succ', List.append_assoc] using h
    rw [h']
    simp [copies_length, tW]
    omega
  rw [p_succ, hp1]
  refine sp_dec S Y ([1,2,1] ++ copies [0,2] m) [0,2] 0
    (Y.length + 4 + 2*m + 1) (Y.length + 1)
    (by simp [S, tW, copies_succ', List.append_assoc])
    (by simp [copies_length]; omega) rfl ?_ ?_
  · simp [List.cons_lt_cons_iff]
  · rw [geAll_append]
    refine ⟨?_, geAll_copies_02_self m [0,2]⟩
    simp only [GeAll, List.cons_append, List.nil_append]
    exact ⟨cons_le_of_lt _ _ _ _ (by decide),
      cons_le_of_lt _ _ _ _ (by decide),
      cons_le_of_lt _ _ _ _ (by decide), trivial⟩

theorem two_copies_D_le_two_one (r : ℕ) (N : List ℕ) :
    2 :: copies [0,2] r ≤ 2 :: 1 :: N := by
  cases r with
  | zero => simpa [copies] using lex_le_append [2] (1 :: N)
  | succ r =>
      rw [copies_succ]
      simp only [List.cons_append, List.nil_append]
      exact cons_le_cons_same 2 _ _ (cons_le_of_lt _ _ _ _ (by decide))

theorem tailsLe_copies_D_to_two_one (r : ℕ) (N : List ℕ) :
    TailsLe 2 (2 :: 1 :: N) (copies [0,2] r) [] := by
  induction r with
  | zero => simp [copies, TailsLe]
  | succ r ih =>
      rw [copies_succ, tailsLe_append]
      refine ⟨?_, ih⟩
      simp only [TailsLe, List.cons_append, List.nil_append]
      exact ⟨fun _ => by simpa using two_copies_D_le_two_one r N,
        by omega, trivial⟩

/-- A terminal `E D^(m+1)` has its cut inside `E`, after every prefix. -/
theorem break_and_cut_final_E_D_run (Y : List ℕ) (m : ℕ) :
    br (Y ++ tE ++ copies [0,2] (m+1)) = 2 ∧
      cut (Y ++ tE ++ copies [0,2] (m+1)) = Y.length + 4 := by
  let S := Y ++ tE ++ copies [0,2] (m+1)
  have hp1 : p S 1 = Y.length + 6 + 2*m + 1 := by
    have h := p_one_final_D (Y ++ tE ++ copies [0,2] m)
    have h' : p S 1 = (Y ++ tE ++ copies [0,2] m).length + 1 := by
      simpa [S, copies_succ', List.append_assoc] using h
    rw [h']
    simp [copies_length, tE]
    omega
  have hp2 : p S 2 = Y.length + 1 := by
    rw [p_succ, hp1]
    refine sp_dec S Y ([1,2,0,2,1] ++ copies [0,2] m) [0,2] 0
      (Y.length + 6 + 2*m + 1) (Y.length + 1)
      (by simp [S, tE, copies_succ', List.append_assoc])
      (by simp [copies_length]; omega) rfl ?_ ?_
    · simp [List.cons_lt_cons_iff]
    · rw [geAll_append]
      refine ⟨?_, geAll_copies_02_self m [0,2]⟩
      simp only [GeAll, List.cons_append, List.nil_append]
      refine ⟨cons_le_of_lt _ _ _ _ (by decide),
        cons_le_of_lt _ _ _ _ (by decide), ?_,
        cons_le_of_lt _ _ _ _ (by decide),
        cons_le_of_lt _ _ _ _ (by decide), trivial⟩
      simpa using
        lex_le_append [0,2] (1 :: (copies [0,2] m ++ [0,2]))
  have hh : entry S S.length = 2 :=
    entry_last S (Y ++ tE ++ copies [0,2] m ++ [0]) 2
      (by simp [S, copies_succ', List.append_assoc])
  have hm2 : mbp S (Y.length + 1) = Y.length + 4 := by
    refine mbp_dec S Y [0,1,2] ([2,1] ++ copies [0,2] (m+1)) 0 2
      (Y.length + 1) (Y.length + 4)
      (by simp [S, tE, List.append_assoc]) rfl (by simp) (by simp) hh
      (by decide) ?_
    rw [tailsLe_append]
    constructor
    · simp only [TailsLe, List.cons_append, List.nil_append]
      exact ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide),
        fun _ => cons_le_cons_same 2 _ _ (cons_le_of_lt _ _ _ _ (by decide)),
        fun _ => by omega, trivial⟩
    · simp only [TailsLe, List.cons_append, List.nil_append]
      refine ⟨fun _ => by simp, fun _ => by omega, fun _ => ?_, ?_⟩
      · rw [copies_succ]
        simp only [List.cons_append, List.nil_append]
        exact cons_le_of_lt _ _ _ _ (by decide)
      · exact tailsLe_copies_D_to_two_one (m+1) (copies [0,2] (m+1))
  have hf2 : fbp S 2 = Y.length + 4 := by simp [fbp, hp2, hm2]
  have he0 : entry S (Y.length + 4) = 0 :=
    entry_at S Y (tE ++ copies [0,2] (m+1)) 3 _ (by simp [S]) rfl (by simp [tE])
  have he1 : entry S (Y.length + 1) = 0 :=
    entry_at S Y (tE ++ copies [0,2] (m+1)) 0 _ (by simp [S]) rfl (by simp [tE])
  have hbr : br S = 2 := br_eq_two_of_breakAt S (by simp [S, tE, copies_length]; omega)
    (breakAt_two_of_low S (Y.length + 4) (by rw [hp2]; omega)
      (by rw [hf2]) (by rw [hp2, he0, he1]))
  exact ⟨hbr, by rw [cut, hbr, hf2]⟩

theorem br_final_E_D_run (Y : List ℕ) (m : ℕ) :
    br (Y ++ tE ++ copies [0,2] (m+1)) = 2 :=
  (break_and_cut_final_E_D_run Y m).1

theorem cut_final_E_D_run (Y : List ℕ) (m : ℕ) :
    cut (Y ++ tE ++ copies [0,2] (m+1)) = Y.length + 4 :=
  (break_and_cut_final_E_D_run Y m).2

theorem cut_prefix_final_E_D_run (Z U : List ℕ) (m : ℕ) :
    cut (Z ++ tA 0 ++ U ++ tE ++ copies [0,2] (m+1)) =
      Z.length + cut (tA 0 ++ U ++ tE ++ copies [0,2] (m+1)) := by
  have h₁ := cut_final_E_D_run (Z ++ tA 0 ++ U) m
  have h₂ := cut_final_E_D_run (tA 0 ++ U) m
  simp only [List.append_assoc] at h₁ h₂ ⊢
  rw [h₁, h₂]
  simp [List.length_append]
  omega

/-- The cut of `A0 W D^(m+1)` is the first `1` of `W`. -/
theorem break_and_cut_A0_W_D_run (m : ℕ) :
    breakAt (tA 0 ++ tW ++ copies [0,2] (m+1)) 3 ∧
      cut (tA 0 ++ tW ++ copies [0,2] (m+1)) = 5 := by
  let S := tA 0 ++ tW ++ copies [0,2] (m+1)
  have hp2 : p S 2 = 4 := by
    simpa [S, tA, copies] using p_two_final_W_D_run (tA 0) m
  have hp3 : p S 3 = 1 := by
    rw [p_succ, hp2]
    refine sp_dec S [] [1,2] (tW ++ copies [0,2] (m+1)) 0 4 1
      (by simp [S, tA, copies]) (by simp) rfl ?_ ?_
    · simp [tW, List.cons_lt_cons_iff]
    · simp only [GeAll, tW, List.cons_append, List.nil_append]
      exact ⟨cons_le_of_lt _ _ _ _ (by decide),
        cons_le_of_lt _ _ _ _ (by decide), trivial⟩
  have hh : entry S S.length = 2 :=
    entry_last S (tA 0 ++ tW ++ copies [0,2] m ++ [0]) 2
      (by simp [S, copies_succ', List.append_assoc])
  have hm2 : mbp S 4 = 5 := by
    refine mbp_dec S (tA 0) [0] ([2,1] ++ copies [0,2] (m+1)) 1 2
      4 5 (by simp [S, tA, tW, copies]) (by simp [tA, copies])
      (by simp [tA, copies]) (by simp) hh (by decide) ?_
    simp only [TailsLe, List.cons_append, List.nil_append, List.append_nil]
    refine ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide),
      fun _ => by simp, fun _ => by omega, fun _ => ?_, ?_⟩
    · rw [copies_succ]
      simp only [List.cons_append, List.nil_append]
      exact cons_le_of_lt _ _ _ _ (by decide)
    · exact tailsLe_copies_D_to_two_one (m+1) (copies [0,2] (m+1))
  have hm3 : mbp S 1 = 5 := by
    refine mbp_dec S [] [0,1,2,0] ([2,1] ++ copies [0,2] (m+1)) 1 2
      1 5 (by simp [S, tA, tW, copies]) rfl (by simp) (by simp) hh (by decide) ?_
    rw [tailsLe_append]
    constructor
    · simp only [TailsLe, List.cons_append, List.nil_append, List.append_nil]
      exact ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide),
        fun _ => cons_le_cons_same 2 _ _ (cons_le_of_lt _ _ _ _ (by decide)),
        fun _ => by omega,
        fun _ => cons_le_of_lt _ _ _ _ (by decide), trivial⟩
    · simp only [TailsLe, List.cons_append, List.nil_append, List.append_nil]
      have hc : copies [0,2] (m+1) ≤ 2 :: 1 :: copies [0,2] (m+1) := by
        rw [copies_succ]
        simp only [List.cons_append, List.nil_append]
        exact cons_le_of_lt _ _ _ _ (by decide)
      exact ⟨fun _ => le_rfl, fun _ => by omega, fun _ => hc,
        tailsLe_copies_D_to_two_one (m+1) (copies [0,2] (m+1))⟩
  have hf2 : fbp S 2 = 5 := by simp [fbp, hp2, hm2]
  have hf3 : fbp S 3 = 5 := by simp [fbp, hp3, hm3]
  have hb3 : breakAt S 3 := Or.inl (by rw [hf3, hf2])
  refine ⟨hb3, ?_⟩
  by_cases hb2 : breakAt S 2
  · have hbr : br S = 2 := br_eq_two_of_breakAt S (by simp [S,tA,tW,copies_length]) hb2
    rw [cut, hbr, hf2]
  · have hbr : br S = 3 := br_eq_three S (by simp [S,tA,tW,copies_length]) hb2 hb3
    rw [cut, hbr, hf3]

theorem cut_A0_W_D_run (m : ℕ) :
    cut (tA 0 ++ tW ++ copies [0,2] (m+1)) = 5 :=
  (break_and_cut_A0_W_D_run m).2

theorem head_lt_parent_one_final_W (U : List ℕ) (hU : U = [] ∨ ∃ V, U = 0 :: V) :
    let T := tA 0 ++ U ++ tW
    1 < p T 1 ∧ suf T 1 < suf T (p T 1) := by
  intro T
  have hp : p T 1 = (tA 0 ++ U).length + 1 := by
    simpa [T, List.append_assoc] using p_one_final_W (tA 0 ++ U)
  have hs : suf T (p T 1) = tW := by
    rw [hp]
    simpa [T, List.append_assoc] using suf_app (tA 0 ++ U) tW 0
  refine ⟨by rw [hp]; simp [tA, copies], ?_⟩
  rw [hs]
  rcases hU with rfl | ⟨V, rfl⟩
  · simp [suf, T, tA, tW, copies, List.cons_lt_cons_iff]
  · simp [suf, T, tA, tW, copies, List.cons_lt_cons_iff]

theorem head_lt_parent_two_final_W_D_run (U : List ℕ) (m : ℕ)
    (hU : U = [] ∨ ∃ V, U = 0 :: V) :
    let T := tA 0 ++ U ++ tW ++ copies [0,2] (m+1)
    1 < p T 2 ∧ suf T 1 < suf T (p T 2) := by
  intro T
  have hp : p T 2 = (tA 0 ++ U).length + 1 := by
    simpa [T, List.append_assoc] using p_two_final_W_D_run (tA 0 ++ U) m
  have hs : suf T (p T 2) = tW ++ copies [0,2] (m+1) := by
    rw [hp]
    simpa [T, List.append_assoc] using
      suf_app (tA 0 ++ U) (tW ++ copies [0,2] (m+1)) 0
  refine ⟨by rw [hp]; simp [tA, copies], ?_⟩
  rw [hs]
  rcases hU with rfl | ⟨V, rfl⟩
  · simp [suf, T, tA, tW, copies, List.cons_lt_cons_iff]
  · simp [suf, T, tA, tW, copies, List.cons_lt_cons_iff]

/-- The second parent search has a strict head candidate for every nonempty token word. -/
theorem head_lt_parent_one_word (w : List PrefixTok) (hw : w ≠ []) :
    let T := tA 0 ++ PrefixTok.rawWord w
    1 < p T 1 ∧ suf T 1 < suf T (p T 1) := by
  obtain ⟨v, t, rfl⟩ := word_end_decomp w hw
  have hshape : PrefixTok.rawWord (v ++ [t]) = PrefixTok.rawWord v ++ t.raw := by
    simp [rawWord_append, rawWord_singleton]
  rw [hshape]
  cases t with
  | D =>
      simpa [PrefixTok.raw, List.append_assoc] using
        head_lt_parent_one_final_D (PrefixTok.rawWord v)
  | E =>
      simpa [PrefixTok.raw, List.append_assoc] using
        head_lt_parent_one_final_E (PrefixTok.rawWord v)
  | W =>
      have hU : PrefixTok.rawWord v = [] ∨ ∃ V, PrefixTok.rawWord v = 0 :: V := by
        by_cases hv : v = []
        · left; simp [hv, PrefixTok.rawWord]
        · right; exact rawWord_starts_zero v hv
      simpa [PrefixTok.raw, List.append_assoc] using
        head_lt_parent_one_final_W (PrefixTok.rawWord v) hU
  | A k =>
      cases k with
      | zero =>
          simpa [PrefixTok.raw, List.append_assoc] using
            head_lt_parent_one_final_A0 (PrefixTok.rawWord v)
      | succ k =>
          simpa [PrefixTok.raw, List.append_assoc] using
            head_lt_parent_one_final_A_succ (PrefixTok.rawWord v) k

/-- If the word ends in `D`, its second parent is at a complete `012` head. -/
theorem p_two_final_D_head (v : List PrefixTok) :
    let T := tA 0 ++ PrefixTok.rawWord (v ++ [.D])
    ∃ r, suf T (p T 2) = [0,1,2] ++ r := by
  intro T
  have hword : v ++ [.D] ≠ [] := by simp
  obtain ⟨hp1, hs1⟩ := head_lt_parent_one_word (v ++ [.D]) hword
  have hp1' : 1 < p T 1 := by simpa [T] using hp1
  have hs1' : suf T 1 < suf T (p T 1) := by simpa [T] using hs1
  obtain ⟨hp2lo, hp2lt, hp2s⟩ :=
    sp_result_candidate_of_one T (p T 1) hp1' hs1'
  have hp2 : p T 2 = sp T (p T 1) := p_succ T 1
  have hsafe : ZeroSafe T := by
    simpa [T, tA, copies] using zeroSafe_append
      (ZeroSafe.zero12 ZeroSafe.nil) (zeroSafe_rawWord (v ++ [.D]))
  have hsafe2 : ZeroSafe (suf T (p T 2)) := by
    simpa only [suf] using zeroSafe_drop hsafe (p T 2 - 1)
  have hL : 1 ≤ T.length := by simp [T, tA]
  have hp2bounds := p_bounds T hL 2
  have hne : suf T (p T 2) ≠ [] := by
    have h : p T 2 - 1 < T.length := by omega
    have hs := suf_ne_nil T (p T 2 - 1) h
    simpa [show p T 2 - 1 + 1 = p T 2 by omega] using hs
  have hlast : suf T (p T 1) = [0,2] := by
    have h := p_one_final_D (tA 0 ++ PrefixTok.rawWord v)
    rw [show T = (tA 0 ++ PrefixTok.rawWord v) ++ [0,2] by
      simp [T, PrefixTok.rawWord, PrefixTok.raw,
        List.append_assoc]]
    rw [h]
    simpa using suf_app (tA 0 ++ PrefixTok.rawWord v) [0,2] 0
  have hlt : suf T (p T 2) < [0,2] := by
    rw [hlast] at hp2s
    simpa only [hp2] using hp2s
  exact zeroSafe_lt_final_D hsafe2 hne hlt

/-- A complete `012` token after the initial `A0` is below a final positive-depth `A`. -/
theorem head_lt_final_A_succ (U : List ℕ) (hU : ∃ V, U = [0,1,2] ++ V)
    (k : ℕ) :
    suf (tA 0 ++ U ++ tA (k+1)) 1 < tA (k+1) := by
  obtain ⟨V, rfl⟩ := hU
  have h : (1 :: 2 :: (V ++ tA (k+1))) < (2 :: copies [0,2] k) :=
    cons_lt_of_lt 1 2 _ _ (by decide)
  have h' := append_lt_append_left [0,1,2,0] _ _ h
  convert h' using 1 <;> simp [suf, tA, copies]
  simpa [copies] using (copies_succ [0,2] k)

/-- The head dominates stage two whenever the final token is `A_(k+1)`. -/
theorem head_lt_parent_two_final_A_succ (t : PrefixTok) (w : List PrefixTok)
    (ht : t ≠ .D) (k : ℕ) :
    let T := tA 0 ++ PrefixTok.rawWord (t :: w) ++ tA (k+1)
    1 < p T 2 ∧ suf T 1 < suf T (p T 2) := by
  intro T
  have hp : p T 2 = (tA 0 ++ PrefixTok.rawWord (t :: w)).length + 1 := by
    simpa [T, List.append_assoc] using stage2_A (tA 0 ++ PrefixTok.rawWord (t :: w)) k |>.1
  have hs : suf T (p T 2) = tA (k+1) := by
    rw [hp]
    simpa [T, List.append_assoc] using
      suf_app (tA 0 ++ PrefixTok.rawWord (t :: w)) (tA (k+1)) 0
  refine ⟨by rw [hp]; simp [tA, copies], ?_⟩
  rw [hs]
  have hu := rawWord_head_nonD t w ht
  simpa [T, List.append_assoc] using head_lt_final_A_succ (PrefixTok.rawWord (t :: w)) hu k

theorem head_lt_parent_two_A0_A_succ (k : ℕ) :
    let T := tA 0 ++ tA (k+1)
    1 < p T 2 ∧ suf T 1 < suf T (p T 2) := by
  intro T
  have hp : p T 2 = (tA 0).length + 1 := by
    simpa [T] using (stage2_A (tA 0) k).1
  have hs : suf T (p T 2) = tA (k+1) := by
    rw [hp]
    simpa [T] using suf_app (tA 0) (tA (k+1)) 0
  refine ⟨by rw [hp]; simp [tA, copies], ?_⟩
  rw [hs]
  have h : (1 :: 2 :: copies [0,2] (k+1)) < (2 :: copies [0,2] k) :=
    cons_lt_of_lt 1 2 _ _ (by decide)
  have h' := append_lt_append_left [0,1,2,0] _ _ h
  convert h' using 1 <;> simp [T, suf, tA, copies]
  simpa [copies] using (copies_succ [0,2] k)

/-- Before a final positive-depth `A`, stage three reaches an earlier `0120` head. -/
theorem p_three_final_A_succ_shape (t : PrefixTok) (w : List PrefixTok)
    (ht : t ≠ .D) (k : ℕ) :
    let T := tA 0 ++ PrefixTok.rawWord (t :: w) ++ tA (k+1)
    ∃ R, suf T (p T 3) = [0,1,2,0] ++ R := by
  intro T
  obtain ⟨hqlow, hhead⟩ := head_lt_parent_two_final_A_succ t w ht k
  have hqlo : 1 < p T 2 := by simpa [T] using hqlow
  have hhead' : suf T 1 < suf T (p T 2) := by simpa [T] using hhead
  obtain ⟨hrlo, hrq, hrlt⟩ := sp_result_candidate_of_one T (p T 2) hqlo hhead'
  have hrEq : p T 3 = sp T (p T 2) := p_succ T 2
  have hrq' : p T 3 < p T 2 := by rw [hrEq]; exact hrq
  have hrlt' : suf T (p T 3) < suf T (p T 2) := by
    rw [hrEq]
    exact hrlt
  have hq : p T 2 = (tA 0 ++ PrefixTok.rawWord (t :: w)).length + 1 := by
    simpa [T, List.append_assoc] using stage2_A (tA 0 ++ PrefixTok.rawWord (t :: w)) k |>.1
  have hqshape : suf T (p T 2) = tA (k+1) := by
    rw [hq]
    simpa [T, List.append_assoc] using
      suf_app (tA 0 ++ PrefixTok.rawWord (t :: w)) (tA (k+1)) 0
  have hsafe : ZeroSafe T := by
    simpa [T, tA, copies, List.append_assoc] using zeroSafe_append
      (zeroSafe_append (ZeroSafe.zero12 ZeroSafe.nil) (zeroSafe_rawWord (t :: w)))
      (ZeroSafe.zero12 (zeroSafe_D_copies (k+1)))
  have hsafe_r : ZeroSafe (suf T (p T 3)) := by
    simpa only [suf] using zeroSafe_drop hsafe (p T 3 - 1)
  have hL : 1 ≤ T.length := by simp [T, tA]
  have hrlo' : 1 ≤ p T 3 := (p_bounds T hL 3).1
  have hqlo' : 1 ≤ p T 2 := (p_bounds T hL 2).1
  have hrhigh : p T 3 ≤ T.length := (p_bounds T hL 3).2
  have hqhigh : p T 2 ≤ T.length := (p_bounds T hL 2).2
  have hlen : (suf T (p T 2)).length < (suf T (p T 3)).length := by
    have h1 := suf_length T (p T 2 - 1)
    have h2 := suf_length T (p T 3 - 1)
    rw [show p T 2 - 1 + 1 = p T 2 by omega] at h1
    rw [show p T 3 - 1 + 1 = p T 3 by omega] at h2
    omega
  rw [hqshape] at hrlt' hlen
  have hshape := zeroSafe_lt_A_succ_shape hsafe_r
    (by simpa [tA, copies_succ] using hrlt')
    (by simpa [tA, copies_succ] using hlen)
  exact hshape

/-- The parent path shifts while each scan has a strict local predecessor. -/
theorem p_prefix_shift_of_candidates (Z T : List ℕ) (i : ℕ)
    (hc : ∀ j < i, ∃ a, 1 ≤ a ∧ a < p T j ∧
      suf T a < suf T (p T j) ∧ sp T (p T j) = a) :
    p (Z ++ T) i = Z.length + p T i := by
  induction i with
  | zero => simp [p]
  | succ i ih =>
      have hprev : ∀ j < i, ∃ a, 1 ≤ a ∧ a < p T j ∧
          suf T a < suf T (p T j) ∧ sp T (p T j) = a := by
        intro j hj
        exact hc j (by omega)
      obtain ⟨a, ha, hax, hlt, hsp⟩ := hc i (by omega)
      rw [p_succ, ih hprev, p_succ]
      simpa only [hsp] using sp_prefix_shift_of_candidate Z T (p T i) a ha hax hlt hsp

theorem p_one_prefix_shift_A0 (Z U : List ℕ) (a : ℕ) :
    p (Z ++ tA 0 ++ U ++ [a+1]) 1 =
      Z.length + p (tA 0 ++ U ++ [a+1]) 1 := by
  have h := p_prefix_shift_of_candidates Z (tA 0 ++ U ++ [a+1]) 1 ?_
  · simpa only [List.append_assoc] using h
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact first_parent_candidate U a

/-- The first two parent steps shift for every nonempty token word. -/
theorem p_two_prefix_shift_word (Z : List ℕ) (w : List PrefixTok) (hw : w ≠ []) :
    p (Z ++ tA 0 ++ PrefixTok.rawWord w) 2 =
      Z.length + p (tA 0 ++ PrefixTok.rawWord w) 2 := by
  let T := tA 0 ++ PrefixTok.rawWord w
  have hc : ∀ j < 2, ∃ r, 1 ≤ r ∧ r < p T j ∧
      suf T r < suf T (p T j) ∧ sp T (p T j) = r := by
    intro j hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · obtain ⟨u, a, hraw⟩ := rawWord_ends_positive w hw
      simpa [T, hraw, List.append_assoc] using first_parent_candidate u a
    · obtain ⟨hp, hs⟩ := head_lt_parent_one_word w hw
      have hp' : 1 < p T 1 := by simpa [T] using hp
      have hs' : suf T 1 < suf T (p T 1) := by simpa [T] using hs
      obtain ⟨hr1, hrp, hlt⟩ := sp_result_candidate_of_one T (p T 1) hp' hs'
      exact ⟨sp T (p T 1), hr1, hrp, hlt, rfl⟩
  have h := p_prefix_shift_of_candidates Z T 2 hc
  simpa [T, List.append_assoc] using h

/-- The right-to-left record scan is local once its start is inside `T`. -/
theorem mbp_prefix_shift (Z T : List ℕ) (x : ℕ) (hx : 1 ≤ x) (hT : T ≠ []) :
    mbp (Z ++ T) (Z.length + x) = Z.length + mbp T x := by
  have hlen : (Z ++ T).length = Z.length + T.length := by simp
  have hlocal := (mbp_eq_iff T x (mbp T x)).1 rfl
  apply (mbp_eq_iff (Z ++ T) (Z.length + x) (Z.length + mbp T x)).2
  rcases hlocal with hcase | hcase
  · left
    obtain ⟨hxr, hr, hbest⟩ := hcase
    refine ⟨by omega, (candidate_prefix_shift Z T _ (by have := hr.1; omega) hT).2 hr,
      ?_⟩
    intro j hj hcan
    let q := j - Z.length
    have hq : 1 ≤ q := by dsimp [q]; omega
    have hjq : j = Z.length + q := by dsimp [q]; omega
    have hqc : Candidate T q :=
      (candidate_prefix_shift Z T q hq hT).1 (by simpa only [hjq] using hcan)
    have hqx : x ≤ q := by omega
    have hle := hbest q hqx hqc
    simpa only [hjq, show Z.length + q + 1 = Z.length + (q+1) by omega,
      show Z.length + mbp T x + 1 = Z.length + (mbp T x + 1) by omega,
      suf_prefix_shift Z T (q+1) (by omega),
      suf_prefix_shift Z T (mbp T x + 1) (by omega)] using hle
  · right
    obtain ⟨hr, hno⟩ := hcase
    refine ⟨by rw [hr, hlen], ?_⟩
    intro j hj hcan
    let q := j - Z.length
    have hq : 1 ≤ q := by dsimp [q]; omega
    have hjq : j = Z.length + q := by dsimp [q]; omega
    have hqc : Candidate T q :=
      (candidate_prefix_shift Z T q hq hT).1 (by simpa only [hjq] using hcan)
    exact hno q (by omega) hqc

theorem fbp_prefix_shift (Z T : List ℕ) (i : ℕ) (hT : T ≠ [])
    (hp : p (Z ++ T) i = Z.length + p T i) :
    fbp (Z ++ T) i = Z.length + fbp T i := by
  have hlen : 1 ≤ T.length := List.length_pos_iff.mpr hT
  simp only [fbp, hp]
  exact mbp_prefix_shift Z T (p T i) (p_bounds T hlen i).1 hT

/-- The break predicate is local when the two parent positions shift. -/
theorem breakAt_prefix_shift (Z T : List ℕ) (i : ℕ) (hi : 1 ≤ i) (hT : T ≠ [])
    (hpi : p (Z ++ T) i = Z.length + p T i)
    (hpp : p (Z ++ T) (i-1) = Z.length + p T (i-1)) :
    breakAt (Z ++ T) i ↔ breakAt T i := by
  have hlen : 1 ≤ T.length := List.length_pos_iff.mpr hT
  have hfi := fbp_prefix_shift Z T i hT hpi
  have hfp := fbp_prefix_shift Z T (i-1) hT hpp
  rw [breakAt_iff (Z ++ T) (by simp; omega) i hi,
    breakAt_iff T hlen i hi]
  constructor
  · rintro (heq | ⟨j, hpj, hj, he⟩)
    · left; rw [hfi, hfp] at heq; omega
    · right
      let q := j - Z.length
      have hpT := (p_bounds T hlen i).1
      have hq : 1 ≤ q := by dsimp [q]; rw [hpi] at hpj; omega
      have hjq : j = Z.length + q := by dsimp [q]; rw [hpi] at hpj; omega
      have hqT : q ≤ T.length := by rw [hfi] at hj; have := fbp_le_length T i; omega
      have he' : entry T q ≤ entry T (p T i) := by
        rw [hjq, hpi, entry_prefix_shift Z T q hq hqT,
          entry_prefix_shift Z T (p T i) hpT (p_bounds T hlen i).2] at he
        exact he
      exact ⟨q, by rw [hpi] at hpj; omega, by rw [hfi] at hj; omega, he'⟩
  · rintro (heq | ⟨q, hpq, hqf, he⟩)
    · left; rw [hfi, hfp]; omega
    · right
      have hq : 1 ≤ q := by have := (p_bounds T hlen i).1; omega
      have hqT : q ≤ T.length := (hqf.trans (fbp_le_length T i))
      refine ⟨Z.length + q, by rw [hpi]; omega, by rw [hfi]; omega, ?_⟩
      rw [hpi, entry_prefix_shift Z T q hq hqT,
        entry_prefix_shift Z T (p T i) (p_bounds T hlen i).1 (p_bounds T hlen i).2]
      exact he

/-- Stage three breaks if a new record must cross a low entry three places after its parent. -/
theorem breakAt_three_of_record_gap (S : Sequence) (q r : ℕ)
    (hL : 1 ≤ S.length) (hq : p S 2 = q) (hr : p S 3 = r)
    (hrq : r < q) (hcan : Candidate S (q+1))
    (hfirst : suf S (r+1) < suf S (q+2))
    (hsecond : suf S (r+2) < suf S (q+2))
    (hthird : ¬Candidate S (r+2))
    (hlow : entry S (r+3) ≤ entry S r) : breakAt S 3 := by
  by_cases hmq : q ≤ mbp S r
  · have hm : mbp S q = mbp S r := by
      apply mbp_eq_of_argmax S q (mbp S r) hmq
      · exact mbp_candidate_of_exists S r (q+1) (by omega) hcan
      · intro j hj hjc
        exact ((mbp_spec S r).2.2.2 j (by omega) hjc).1
    apply (breakAt_iff S hL 3 (by omega)).2
    left
    simp [fbp, hq, hr, hm]
  · have hmcan : Candidate S (mbp S r) :=
      mbp_candidate_of_exists S r (q+1) (by omega) hcan
    have hbest : suf S (q+2) ≤ suf S (mbp S r+1) :=
      ((mbp_spec S r).2.2.2 (q+1) (by omega) hcan).1
    have hmlo : r ≤ mbp S r := by
      have hmin := (mbp_spec S r).1
      have hrL := (p_bounds S hL 3).2
      rw [hr] at hrL
      omega
    have hmgt : r+3 ≤ mbp S r := by
      have hne0 : mbp S r ≠ r := by
        intro he
        rw [he] at hbest
        exact (not_lt_of_ge hbest) hfirst
      have hne1 : mbp S r ≠ r+1 := by
        intro he
        rw [he] at hbest
        exact (not_lt_of_ge hbest) hsecond
      have hne2 : mbp S r ≠ r+2 := by
        intro he
        exact hthird (he ▸ hmcan)
      omega
    apply (breakAt_iff S hL 3 (by omega)).2
    right
    refine ⟨r+3, by rw [hr]; omega, ?_, ?_⟩
    · rw [fbp, hr]
      exact hmgt
    · rw [hr]
      exact hlow

theorem breakAt_three_of_record_gap4 (S : Sequence) (q r : ℕ)
    (hL : 1 ≤ S.length) (hq : p S 2 = q) (hr : p S 3 = r)
    (hrq : r < q) (hcan : Candidate S (q+1))
    (hfirst : suf S (r+1) < suf S (q+2))
    (hsecond : suf S (r+2) < suf S (q+2))
    (hthird : ¬Candidate S (r+2))
    (hfourth : suf S (r+4) < suf S (q+2))
    (hlow : entry S (r+4) ≤ entry S r) : breakAt S 3 := by
  by_cases hmq : q ≤ mbp S r
  · have hm : mbp S q = mbp S r := by
      apply mbp_eq_of_argmax S q (mbp S r) hmq
      · exact mbp_candidate_of_exists S r (q+1) (by omega) hcan
      · intro j hj hjc
        exact ((mbp_spec S r).2.2.2 j (by omega) hjc).1
    apply (breakAt_iff S hL 3 (by omega)).2
    left
    simp [fbp, hq, hr, hm]
  · have hmcan : Candidate S (mbp S r) :=
      mbp_candidate_of_exists S r (q+1) (by omega) hcan
    have hbest : suf S (q+2) ≤ suf S (mbp S r+1) :=
      ((mbp_spec S r).2.2.2 (q+1) (by omega) hcan).1
    have hmlo : r ≤ mbp S r := by
      have hmin := (mbp_spec S r).1
      have hrL := (p_bounds S hL 3).2
      rw [hr] at hrL
      omega
    have hmgt : r+4 ≤ mbp S r := by
      have hne0 : mbp S r ≠ r := by
        intro he
        rw [he] at hbest
        exact (not_lt_of_ge hbest) hfirst
      have hne1 : mbp S r ≠ r+1 := by
        intro he
        rw [he] at hbest
        exact (not_lt_of_ge hbest) hsecond
      have hne2 : mbp S r ≠ r+2 := by
        intro he
        exact hthird (he ▸ hmcan)
      have hne3 : mbp S r ≠ r+3 := by
        intro he
        rw [he] at hbest
        exact (not_lt_of_ge hbest) hfourth
      omega
    apply (breakAt_iff S hL 3 (by omega)).2
    right
    refine ⟨r+4, by rw [hr]; omega, ?_, ?_⟩
    · rw [fbp, hr]
      exact hmgt
    · rw [hr]
      exact hlow

/-- With terminal entry one, any new record at stage two is a later zero. -/
theorem breakAt_two_of_zero_record (S : Sequence) (q r : ℕ)
    (hL : 1 ≤ S.length) (hq : p S 1 = q) (hr : p S 2 = r)
    (hrq : r < q) (hcan : Candidate S q) (hrecord : mbp S q = q)
    (hstrict : suf S (r+1) < suf S (q+1))
    (hterminal : entry S S.length = 1) (her : entry S r = 0) :
    breakAt S 2 := by
  by_cases heq : mbp S r = q
  · apply (breakAt_iff S hL 2 (by omega)).2
    left
    simp [fbp, hq, hr, heq, hrecord]
  · have hmcan : Candidate S (mbp S r) :=
      mbp_candidate_of_exists S r q (by omega) hcan
    have hmlo : r ≤ mbp S r := by
      have hm := (mbp_spec S r).1
      have hrhi := (p_bounds S hL 2).2
      rw [hr] at hrhi
      omega
    have hmhi : mbp S r < q := by
      by_contra hn
      have hqm : q ≤ mbp S r := by omega
      have hm : mbp S q = mbp S r := by
        apply mbp_eq_of_argmax S q (mbp S r) hqm hmcan
        intro j hj hjc
        exact ((mbp_spec S r).2.2.2 j (by omega) hjc).1
      rw [hrecord] at hm
      exact heq hm.symm
    have hmgt : r < mbp S r := by
      by_contra hn
      have he : mbp S r = r := by omega
      have hbest := ((mbp_spec S r).2.2.2 q (by omega) hcan).1
      rw [he] at hbest
      exact (not_lt_of_ge hbest) hstrict
    have hem : entry S (mbp S r) = 0 := by
      have hlt := hmcan.2
      rw [hterminal] at hlt
      omega
    apply (breakAt_iff S hL 2 (by omega)).2
    right
    refine ⟨mbp S r, by rw [hr]; exact hmgt, ?_, ?_⟩
    · rw [fbp, hr]
    · rw [hr, hem, her]

/-- The local record gap always closes at stage three for a final `A_(k+1)`. -/
theorem breakAt_three_final_A_succ (t : PrefixTok) (w : List PrefixTok)
    (ht : t ≠ .D) (k : ℕ) :
    breakAt (tA 0 ++ PrefixTok.rawWord (t :: w) ++ tA (k+1)) 3 := by
  let Y := tA 0 ++ PrefixTok.rawWord (t :: w)
  let S := Y ++ tA (k+1)
  let q := p S 2
  let r := p S 3
  have hq : q = Y.length + 1 := by
    simpa [S, q] using (stage2_A Y k).1
  have hqsuf : suf S q = tA (k+1) := by
    rw [hq]
    simpa [S] using suf_app Y (tA (k+1)) 0
  obtain ⟨R, hrsuf⟩ := p_three_final_A_succ_shape t w ht k
  change suf S r = [0,1,2,0] ++ R at hrsuf
  have hL : 1 ≤ S.length := by simp [S, Y, tA]
  have hrlo : 1 ≤ r := (p_bounds S hL 3).1
  have hrhi : r ≤ S.length := (p_bounds S hL 3).2
  have hqlo : 1 ≤ q := (p_bounds S hL 2).1
  have hqhi : q ≤ S.length := (p_bounds S hL 2).2
  have hrq : r < q := by
    obtain ⟨h1, h2⟩ := head_lt_parent_two_final_A_succ t w ht k
    have h1' : 1 < q := by simpa [S, Y, q] using h1
    have h2' : suf S 1 < suf S q := by simpa [S, Y, q] using h2
    obtain ⟨_, h, _⟩ := sp_result_candidate_of_one S q h1' h2'
    simpa [r, q, p_succ] using h
  have hr4 : r+3 ≤ S.length := by
    have h := suf_length S (r-1)
    rw [show r-1+1 = r by omega, hrsuf] at h
    simp at h
    omega
  have hrs1 : suf S (r+1) = [1,2,0] ++ R := by
    rw [suf_shift S r 1 hrlo, hrsuf]
    rfl
  have hrs2 : suf S (r+2) = [2,0] ++ R := by
    rw [suf_shift S r 2 hrlo, hrsuf]
    rfl
  have hrs3 : suf S (r+3) = 0 :: R := by
    rw [suf_shift S r 3 hrlo, hrsuf]
    rfl
  have hqs2 : suf S (q+2) = 2 :: 0 :: 2 :: copies [0,2] k := by
    rw [suf_shift S q 2 hqlo, hqsuf]
    simp [tA, copies_succ]
  have hfirst : suf S (r+1) < suf S (q+2) := by
    rw [hrs1, hqs2]
    exact cons_lt_of_lt 1 2 _ _ (by decide)
  have hsecond : suf S (r+2) < suf S (q+2) := by
    have hparent : suf S r < suf S q := by
      have h1 := head_lt_parent_two_final_A_succ t w ht k
      have h1' : 1 < q := by simpa [S, Y, q] using h1.1
      have h2' : suf S 1 < suf S q := by simpa [S, Y, q] using h1.2
      obtain ⟨_, _, h⟩ := sp_result_candidate_of_one S q h1' h2'
      simpa [r, q, p_succ] using h
    rw [hrsuf, hqsuf] at hparent
    rw [hrs2, hqs2]
    simpa [tA, copies_succ, List.cons_lt_cons_iff] using hparent
  have hlast : entry S S.length = 2 :=
    entry_last S (Y ++ tA k ++ [0]) 2 (by simp [S, tA_succ, List.append_assoc])
  have hq1 : entry S (q+1) = 1 := by
    rw [hq]
    simpa [S, tA] using entry_at S Y (tA (k+1)) 1 (Y.length+2)
      (by simp [S]) (by omega) (by simp [tA])
  have hqcan : Candidate S (q+1) := by
    constructor
    · rw [hq]; simp [S, tA, copies_length]; omega
    · rw [hq1, hlast]; omega
  have hr0 : entry S r = 0 := entry_of_suf_cons S r 0 _ hrlo hrhi hrsuf
  have hr2 : entry S (r+2) = 2 :=
    entry_of_suf_cons S (r+2) 2 _ (by omega) (by omega) hrs2
  have hr3 : entry S (r+3) = 0 :=
    entry_of_suf_cons S (r+3) 0 R (by omega) hr4 hrs3
  have hr2no : ¬Candidate S (r+2) := by
    intro hc
    have := hc.2
    rw [hr2, hlast] at this
    omega
  have hb := breakAt_three_of_record_gap S q r hL rfl rfl hrq hqcan
    hfirst hsecond hr2no (by rw [hr0, hr3])
  simpa [S, Y] using hb

theorem br_final_A_succ (Y : List ℕ) (k : ℕ)
    (hb3 : breakAt (Y ++ tA (k+1)) 3) :
    br (Y ++ tA (k+1)) = 3 := by
  exact br_eq_three _ (by simp [tA, copies_length]; omega)
    (stage2_A Y k).2.2 hb3

/-- A final `W` always causes the second-stage break after an initial `A0`. -/
theorem breakAt_two_final_W (v : List PrefixTok) :
    breakAt (tA 0 ++ PrefixTok.rawWord v ++ tW) 2 := by
  let Y := tA 0 ++ PrefixTok.rawWord v
  let S := Y ++ tW
  let q := p S 1
  let r := p S 2
  have hq : q = Y.length + 1 := by
    simpa [S, q, List.append_assoc] using p_one_final_W Y
  have hqsuf : suf S q = tW := by
    rw [hq]
    simpa [S] using suf_app Y tW 0
  have hL : 1 ≤ S.length := by simp [S, Y, tA]
  have hqlo : 1 ≤ q := (p_bounds S hL 1).1
  have hrlo : 1 ≤ r := (p_bounds S hL 2).1
  have hrhi : r ≤ S.length := (p_bounds S hL 2).2
  have hhead : 1 < q ∧ suf S 1 < suf S q := by
    have hraw : PrefixTok.rawWord (v ++ [.W]) = PrefixTok.rawWord v ++ tW := by
      rw [rawWord_append, rawWord_singleton]
      rfl
    have h := head_lt_parent_one_word (v ++ [.W]) (by simp)
    rw [hraw] at h
    simpa [S, Y, q, List.append_assoc] using h
  obtain ⟨_, hrq0, hrlt0⟩ := sp_result_candidate_of_one S q hhead.1 hhead.2
  have hrq : r < q := by simpa [r, q, p_succ] using hrq0
  have hrlt : suf S r < suf S q := by simpa [r, q, p_succ] using hrlt0
  have hsafe : ZeroSafe S := by
    simpa [S, Y, tA, copies, tW, List.append_assoc] using zeroSafe_append
      (zeroSafe_append (ZeroSafe.zero12 ZeroSafe.nil) (zeroSafe_rawWord v))
      (ZeroSafe.zero12 (ZeroSafe.one ZeroSafe.nil))
  have hsafe_r : ZeroSafe (suf S r) := by
    simpa only [suf] using zeroSafe_drop hsafe (r-1)
  have hne : suf S r ≠ [] := by
    have h := suf_ne_nil S (r-1) (by omega)
    simpa [show r-1+1 = r by omega] using h
  rw [hqsuf] at hrlt
  obtain ⟨R, hrsuf⟩ := zeroSafe_lt_W_head hsafe_r hne hrlt
  have hrzero : entry S r = 0 := entry_of_suf_cons S r 0 R hrlo hrhi hrsuf
  have hstrict : suf S (r+1) < suf S (q+1) := by
    have h := hrlt
    rw [hrsuf] at h
    have htail : R < [1,2,1] := by simpa [tW, List.cons_lt_cons_iff] using h
    rw [suf_shift S r 1 hrlo, hrsuf, suf_shift S q 1 hqlo, hqsuf]
    simpa [tW] using htail
  have hlast : entry S S.length = 1 :=
    entry_last S (Y ++ [0,1,2]) 1 (by simp [S, tW])
  have hqzero : entry S q = 0 := by
    rw [hq]
    simpa [S, tW] using entry_at S Y tW 0 (Y.length+1)
      (by simp [S]) (by omega) (by simp [tW])
  have hqcan : Candidate S q := by
    constructor
    · rw [hq]; simp [S, tW]
    · rw [hqzero, hlast]; omega
  have hrecord : mbp S q = q := by
    rw [hq]
    refine mbp_dec S Y [] [1,2,1] 0 1 (Y.length+1) (Y.length+1)
      (by simp [S, tW]) rfl rfl (by simp) hlast (by decide) ?_
    simp [TailsLe]
  have hb := breakAt_two_of_zero_record S q r hL rfl rfl hrq hqcan hrecord
    hstrict hlast hrzero
  simpa [S, Y] using hb

/-- A trailing nonempty `D` run after `W` breaks by stage three. -/
theorem breakAt_three_final_W_D_run (v : List PrefixTok) (m : ℕ) :
    breakAt (tA 0 ++ PrefixTok.rawWord v ++ tW ++ copies [0,2] (m+1)) 3 := by
  let Y := tA 0 ++ PrefixTok.rawWord v
  let S := Y ++ tW ++ copies [0,2] (m+1)
  let q := p S 2
  let r := p S 3
  have hq : q = Y.length + 1 := by
    simpa [S, q, List.append_assoc] using p_two_final_W_D_run Y m
  have hqsuf : suf S q = tW ++ copies [0,2] (m+1) := by
    rw [hq]
    simpa [S, List.append_assoc] using suf_app Y (tW ++ copies [0,2] (m+1)) 0
  have hL : 1 ≤ S.length := by simp [S, Y, tA]
  have hqlo : 1 ≤ q := (p_bounds S hL 2).1
  have hqhi : q ≤ S.length := (p_bounds S hL 2).2
  have hrlo : 1 ≤ r := (p_bounds S hL 3).1
  have hrhi : r ≤ S.length := (p_bounds S hL 3).2
  have hU : PrefixTok.rawWord v = [] ∨ ∃ V, PrefixTok.rawWord v = 0 :: V := by
    by_cases hv : v = []
    · left; simp [hv, PrefixTok.rawWord]
    · right; exact rawWord_starts_zero v hv
  have hhead : 1 < q ∧ suf S 1 < suf S q := by
    simpa [S, Y, q, List.append_assoc] using
      head_lt_parent_two_final_W_D_run (PrefixTok.rawWord v) m hU
  obtain ⟨_, hrq0, hrlt0⟩ := sp_result_candidate_of_one S q hhead.1 hhead.2
  have hrq : r < q := by simpa [r, q, p_succ] using hrq0
  have hrlt : suf S r < suf S q := by simpa [r, q, p_succ] using hrlt0
  let word := (v ++ [.W]) ++ List.replicate (m+1) PrefixTok.D
  have hword : word ≠ [] := by simp [word]
  have hraw : PrefixTok.rawWord word =
      PrefixTok.rawWord v ++ tW ++ copies [0,2] (m+1) := by
    change PrefixTok.rawWord ((v ++ [.W]) ++ List.replicate (m+1) .D) = _
    rw [rawWord_append, rawWord_append, rawWord_singleton, rawWord_replicate_D]
    rfl
  obtain ⟨R0, hR0⟩ := rawWord_starts_zero word hword
  have hsafe : ZeroSafe S := by
    have h := zeroSafe_append (ZeroSafe.zero12 ZeroSafe.nil)
      (zeroSafe_rawWord word)
    simpa [S, Y, tA, copies, hraw, List.append_assoc] using h
  have hbad : NoBad21 S := by
    have h := noBad21_append_zero (tA 0) R0 (noBad21_A 0)
      (by simpa [hR0] using noBad21_rawWord word)
    change NoBad21 (tA 0 ++ (PrefixTok.rawWord v ++ tW ++ copies [0,2] (m+1)))
    rw [← hraw, hR0]
    exact h
  have hsafe_r : ZeroSafe (suf S r) := by
    simpa only [suf] using zeroSafe_drop hsafe (r-1)
  have hbad_r : NoBad21 (suf S r) := by
    simpa only [suf] using noBad21_drop hbad (r-1)
  have hlen : (suf S q).length < (suf S r).length := by
    have h1 := suf_length S (q-1)
    have h2 := suf_length S (r-1)
    rw [show q-1+1=q by omega] at h1
    rw [show r-1+1=r by omega] at h2
    omega
  have hfive : 5 ≤ (suf S r).length := by
    rw [hqsuf] at hlen
    simp [tW, copies_length] at hlen
    omega
  rw [hqsuf] at hrlt
  rcases safe_lt_W_shape hsafe_r hbad_r hrlt hfive with ⟨R, hrsuf⟩ | ⟨R, hrsuf⟩
  · have hr4 : r+3 ≤ S.length := by
      have h := suf_length S (r-1)
      rw [show r-1+1=r by omega, hrsuf] at h
      simp at h
      omega
    have hrs1 : suf S (r+1) = [1,2,0] ++ R := by
      rw [suf_shift S r 1 hrlo, hrsuf]; rfl
    have hrs2 : suf S (r+2) = [2,0] ++ R := by
      rw [suf_shift S r 2 hrlo, hrsuf]; rfl
    have hrs3 : suf S (r+3) = 0 :: R := by
      rw [suf_shift S r 3 hrlo, hrsuf]; rfl
    have hqs2 : suf S (q+2) = 2 :: 1 :: copies [0,2] (m+1) := by
      rw [suf_shift S q 2 hqlo, hqsuf]; simp [tW]
    have hfirst : suf S (r+1) < suf S (q+2) := by
      rw [hrs1, hqs2]
      exact cons_lt_of_lt 1 2 _ _ (by decide)
    have hsecond : suf S (r+2) < suf S (q+2) := by
      rw [hrs2, hqs2]
      simp [List.cons_lt_cons_iff]
    have hlast : entry S S.length = 2 :=
      entry_last S (Y ++ tW ++ copies [0,2] m ++ [0]) 2
        (by simp [S, copies_succ', List.append_assoc])
    have hq1 : entry S (q+1) = 1 := by
      rw [hq]
      simpa [S, tW] using entry_at S Y (tW ++ copies [0,2] (m+1)) 1 (Y.length+2)
        (by simp [S, List.append_assoc]) (by omega) (by simp [tW])
    have hqcan : Candidate S (q+1) := by
      constructor
      · rw [hq]; simp [S, tW, copies_length]; omega
      · rw [hq1, hlast]; omega
    have hr0 : entry S r = 0 := entry_of_suf_cons S r 0 _ hrlo hrhi hrsuf
    have hr2 : entry S (r+2) = 2 :=
      entry_of_suf_cons S (r+2) 2 _ (by omega) (by omega) hrs2
    have hr3 : entry S (r+3) = 0 :=
      entry_of_suf_cons S (r+3) 0 R (by omega) hr4 hrs3
    have hr2no : ¬Candidate S (r+2) := by
      intro hc
      have := hc.2
      rw [hr2, hlast] at this
      omega
    have hb := breakAt_three_of_record_gap S q r hL rfl rfl hrq hqcan
      hfirst hsecond hr2no (by rw [hr0, hr3])
    simpa [S, Y, List.append_assoc] using hb

  · have hr5 : r+4 ≤ S.length := by
      have h := suf_length S (r-1)
      rw [show r-1+1=r by omega, hrsuf] at h
      simp at h
      omega
    have hrs1 : suf S (r+1) = [1,2,1,0] ++ R := by
      rw [suf_shift S r 1 hrlo, hrsuf]; rfl
    have hrs2 : suf S (r+2) = [2,1,0] ++ R := by
      rw [suf_shift S r 2 hrlo, hrsuf]; rfl
    have hrs4 : suf S (r+4) = 0 :: R := by
      rw [suf_shift S r 4 hrlo, hrsuf]; rfl
    have hqs2 : suf S (q+2) = 2 :: 1 :: copies [0,2] (m+1) := by
      rw [suf_shift S q 2 hqlo, hqsuf]; simp [tW]
    have hfirst : suf S (r+1) < suf S (q+2) := by
      rw [hrs1, hqs2]
      exact cons_lt_of_lt 1 2 _ _ (by decide)
    have hsecond : suf S (r+2) < suf S (q+2) := by
      have h := hrlt
      rw [hrsuf] at h
      rw [hrs2, hqs2]
      simpa [tW, copies_succ, List.cons_lt_cons_iff] using h
    have hfourth : suf S (r+4) < suf S (q+2) := by
      rw [hrs4, hqs2]
      exact cons_lt_of_lt 0 2 _ _ (by decide)
    have hlast : entry S S.length = 2 :=
      entry_last S (Y ++ tW ++ copies [0,2] m ++ [0]) 2
        (by simp [S, copies_succ', List.append_assoc])
    have hq1 : entry S (q+1) = 1 := by
      rw [hq]
      simpa [S, tW] using entry_at S Y (tW ++ copies [0,2] (m+1)) 1 (Y.length+2)
        (by simp [S, List.append_assoc]) (by omega) (by simp [tW])
    have hqcan : Candidate S (q+1) := by
      constructor
      · rw [hq]; simp [S, tW, copies_length]; omega
      · rw [hq1, hlast]; omega
    have hr0 : entry S r = 0 := entry_of_suf_cons S r 0 _ hrlo hrhi hrsuf
    have hr2 : entry S (r+2) = 2 :=
      entry_of_suf_cons S (r+2) 2 _ (by omega) (by omega) hrs2
    have hr4 : entry S (r+4) = 0 :=
      entry_of_suf_cons S (r+4) 0 R (by omega) hr5 hrs4
    have hr2no : ¬Candidate S (r+2) := by
      intro hc
      have := hc.2
      rw [hr2, hlast] at this
      omega
    have hb := breakAt_three_of_record_gap4 S q r hL rfl rfl hrq hqcan
      hfirst hsecond hr2no hfourth (by rw [hr0, hr4])
    simpa [S, Y, List.append_assoc] using hb

theorem br_final_W_D_run (v : List PrefixTok) (m : ℕ) :
    br (tA 0 ++ PrefixTok.rawWord v ++ tW ++ copies [0,2] (m+1)) = 2 ∨
      br (tA 0 ++ PrefixTok.rawWord v ++ tW ++ copies [0,2] (m+1)) = 3 := by
  let S := tA 0 ++ PrefixTok.rawWord v ++ tW ++ copies [0,2] (m+1)
  by_cases hb2 : breakAt S 2
  · left
    exact br_eq_two_of_breakAt S (by simp [S, tA, tW, copies_length]) hb2
  · right
    exact br_eq_three S (by simp [S, tA, tW, copies_length]) hb2
      (by simpa [S, List.append_assoc] using breakAt_three_final_W_D_run v m)

/-- Every nonempty token word whose second stage breaks has a prefix-independent cut. -/
theorem cut_prefix_word_break_two (Z : List ℕ) (w : List PrefixTok) (hw : w ≠ [])
    (hb2 : breakAt (tA 0 ++ PrefixTok.rawWord w) 2) :
    cut (Z ++ tA 0 ++ PrefixTok.rawWord w) =
      Z.length + cut (tA 0 ++ PrefixTok.rawWord w) := by
  let T := tA 0 ++ PrefixTok.rawWord w
  have hT : T ≠ [] := by simp [T, tA]
  obtain ⟨u, a, hraw⟩ := rawWord_ends_positive w hw
  have hp1 : p (Z ++ T) 1 = Z.length + p T 1 := by
    simpa [T, hraw, List.append_assoc] using p_one_prefix_shift_A0 Z u a
  have hp2 : p (Z ++ T) 2 = Z.length + p T 2 := by
    simpa [T, List.append_assoc] using p_two_prefix_shift_word Z w hw
  have hbs2 : breakAt (Z ++ T) 2 :=
    (breakAt_prefix_shift Z T 2 (by omega) hT hp2 (by simpa using hp1)).2 hb2
  have hbrS : br (Z ++ T) = 2 :=
    br_eq_two_of_breakAt (Z ++ T) (by simp [T, tA]; omega) hbs2
  have hbrT : br T = 2 := br_eq_two_of_breakAt T (by simp [T, tA]) hb2
  rw [show Z ++ tA 0 ++ PrefixTok.rawWord w = Z ++ T by simp [T, List.append_assoc],
    cut, hbrS, cut, hbrT]
  exact fbp_prefix_shift Z T 2 hT hp2

/-- A certificate up to the first break makes the cut prefix independent. -/
theorem cut_prefix_of_local_certificate (Z T : List ℕ) (b : ℕ)
    (hT : T ≠ []) (hb : 1 < b) (hbL : b ≤ T.length)
    (hbreak : breakAt T b)
    (hno : ∀ i, 1 < i → i < b → ¬breakAt T i)
    (hc : ∀ j < b, ∃ a, 1 ≤ a ∧ a < p T j ∧
      suf T a < suf T (p T j) ∧ sp T (p T j) = a) :
    cut (Z ++ T) = Z.length + cut T := by
  have hp : ∀ i ≤ b, p (Z ++ T) i = Z.length + p T i := by
    intro i hi
    apply p_prefix_shift_of_candidates Z T i
    intro j hj
    exact hc j (by omega)
  have hbrT : br T = b := br_eq_of_first T b hbL hb hbreak hno
  have hbrS : br (Z ++ T) = b := by
    apply br_eq_of_first (Z ++ T) b (by simp; omega) hb
    · exact (breakAt_prefix_shift Z T b (by omega) hT
        (hp b le_rfl) (hp (b-1) (by omega))).2 hbreak
    · intro i hi hib hbi
      exact hno i hi hib ((breakAt_prefix_shift Z T i (by omega) hT
        (hp i (by omega)) (hp (i-1) (by omega))).1 hbi)
  rw [cut, hbrS, cut, hbrT]
  exact fbp_prefix_shift Z T b hT (hp b le_rfl)

/-- A head-suffix inequality is a compact version of the local certificate. -/
theorem cut_prefix_of_head_dominance (Z T : List ℕ) (b : ℕ)
    (hT : T ≠ []) (hb : 1 < b) (hbL : b ≤ T.length)
    (hbreak : breakAt T b)
    (hno : ∀ i, 1 < i → i < b → ¬breakAt T i)
    (hhead : ∀ j < b, 1 < p T j ∧ suf T 1 < suf T (p T j)) :
    cut (Z ++ T) = Z.length + cut T := by
  apply cut_prefix_of_local_certificate Z T b hT hb hbL hbreak hno
  intro j hj
  obtain ⟨hp, hs⟩ := hhead j hj
  obtain ⟨hr1, hrp, hlt⟩ := sp_result_candidate_of_one T (p T j) hp hs
  exact ⟨sp T (p T j), hr1, hrp, hlt, rfl⟩

/-- The third-stage case needs one further head-suffix inequality. -/
theorem cut_prefix_word_break_three (Z : List ℕ) (w : List PrefixTok) (hw : w ≠ [])
    (hnot2 : ¬breakAt (tA 0 ++ PrefixTok.rawWord w) 2)
    (hbreak3 : breakAt (tA 0 ++ PrefixTok.rawWord w) 3)
    (hhead2 : 1 < p (tA 0 ++ PrefixTok.rawWord w) 2 ∧
      suf (tA 0 ++ PrefixTok.rawWord w) 1 <
        suf (tA 0 ++ PrefixTok.rawWord w) (p (tA 0 ++ PrefixTok.rawWord w) 2)) :
    cut (Z ++ tA 0 ++ PrefixTok.rawWord w) =
      Z.length + cut (tA 0 ++ PrefixTok.rawWord w) := by
  let T := tA 0 ++ PrefixTok.rawWord w
  have hT : T ≠ [] := by simp [T, tA]
  have hc : ∀ j < 3, ∃ r, 1 ≤ r ∧ r < p T j ∧
      suf T r < suf T (p T j) ∧ sp T (p T j) = r := by
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl
    · obtain ⟨u, a, hraw⟩ := rawWord_ends_positive w hw
      simpa [T, hraw, List.append_assoc] using first_parent_candidate u a
    · obtain ⟨hp, hs⟩ := head_lt_parent_one_word w hw
      have hp' : 1 < p T 1 := by simpa [T] using hp
      have hs' : suf T 1 < suf T (p T 1) := by simpa [T] using hs
      obtain ⟨hr1, hrp, hlt⟩ := sp_result_candidate_of_one T (p T 1) hp' hs'
      exact ⟨sp T (p T 1), hr1, hrp, hlt, rfl⟩
    · obtain ⟨hr1, hrp, hlt⟩ := sp_result_candidate_of_one T (p T 2)
        (by simpa [T] using hhead2.1) (by simpa [T] using hhead2.2)
      exact ⟨sp T (p T 2), hr1, hrp, hlt, rfl⟩
  have hcut := cut_prefix_of_local_certificate Z T 3 hT (by omega)
    (by simp [T, tA, PrefixTok.rawWord])
    (by simpa [T] using hbreak3)
    (by
      intro i hi hi3
      have hi2 : i = 2 := by omega
      rw [hi2]
      simpa [T] using hnot2) hc
  simpa [T, List.append_assoc] using hcut

theorem cut_prefix_A0_W_D_run (Z : List ℕ) (m : ℕ) :
    cut (Z ++ tA 0 ++ tW ++ copies [0,2] (m+1)) =
      Z.length + cut (tA 0 ++ tW ++ copies [0,2] (m+1)) := by
  let w : List PrefixTok := PrefixTok.W :: List.replicate (m+1) PrefixTok.D
  have hw : w ≠ [] := by simp [w]
  have hraw : PrefixTok.rawWord w = tW ++ copies [0,2] (m+1) := by
    simp [w, PrefixTok.rawWord, PrefixTok.raw, copies]
  have hb3 : breakAt (tA 0 ++ PrefixTok.rawWord w) 3 := by
    simpa [hraw] using (break_and_cut_A0_W_D_run m).1
  have hhead : 1 < p (tA 0 ++ PrefixTok.rawWord w) 2 ∧
      suf (tA 0 ++ PrefixTok.rawWord w) 1 <
        suf (tA 0 ++ PrefixTok.rawWord w) (p (tA 0 ++ PrefixTok.rawWord w) 2) := by
    simpa [hraw] using head_lt_parent_two_final_W_D_run [] m (Or.inl rfl)
  by_cases hb2 : breakAt (tA 0 ++ PrefixTok.rawWord w) 2
  · simpa [hraw, List.append_assoc] using cut_prefix_word_break_two Z w hw hb2
  · simpa [hraw, List.append_assoc] using
      cut_prefix_word_break_three Z w hw hb2 hb3 hhead

/-- The cut shifts with an arbitrary prefix when the word ends in `A0`. -/
theorem cut_prefix_last_A0 (Z U : List ℕ) :
    cut (Z ++ [0,1,2] ++ U ++ tA 0) =
      Z.length + cut ([0,1,2] ++ U ++ tA 0) := by
  have h₁ := (cut_A0 (Z ++ [0,1,2] ++ U)).2.2.2
  have h₂ := (cut_A0 ([0,1,2] ++ U)).2.2.2
  rw [tA] at *
  simp [copies, List.append_assoc] at h₁ h₂ ⊢
  omega

/-- The cut shifts with an arbitrary prefix when the word ends in `E`. -/
theorem cut_prefix_last_E (Z U : List ℕ) :
    cut (Z ++ [0,1,2] ++ U ++ tE) =
      Z.length + cut ([0,1,2] ++ U ++ tE) := by
  have h₁ := (cut_E (Z ++ [0,1,2] ++ U)).2.2.2
  have h₂ := (cut_E ([0,1,2] ++ U)).2.2.2
  simp only [List.append_assoc] at h₁ h₂ ⊢
  rw [h₁, h₂]
  simp [List.length_append]
  omega

/-- The cut shifts with an arbitrary prefix for a nonempty `W` run after `A0`. -/
theorem cut_prefix_W_run (Z : List ℕ) (m : ℕ) :
    cut (Z ++ tA 0 ++ copies tW (m+1)) =
      Z.length + cut (tA 0 ++ copies tW (m+1)) := by
  have h₁ := (law_W_A0 Z m).2.2.1
  have h₂ := (law_W_A0 [] m).2.2.1
  rw [copies_succ']
  simp only [List.nil_append, List.append_assoc] at h₁ h₂ ⊢
  rw [h₁, h₂]
  simp

/-- The cut for two adjacent `A` units, the first being `A0`. -/
theorem break_and_cut_A0_A_succ (Y : List ℕ) (k : ℕ) :
    br (Y ++ tA 0 ++ tA (k+1)) = 3 ∧
      cut (Y ++ tA 0 ++ tA (k+1)) = Y.length + 5 := by
  set S := Y ++ tA 0 ++ tA (k+1) with hS
  obtain ⟨hp2, -, hnb2⟩ := stage2_A (Y ++ tA 0) k
  have hp2' : p S 2 = Y.length + 4 := by
    simpa [S, tA, copies] using hp2
  have hnb2' : ¬breakAt S 2 := by simpa [S] using hnb2
  have hp3 : p S 3 = Y.length + 1 := by
    rw [p_succ, hp2']
    refine sp_dec S Y [1,2] (tA (k+1)) 0 (Y.length + 4) (Y.length + 1)
      (by simp [S, tA, copies]) (by simp) rfl ?_ ?_
    · rw [tA, copies_succ]
      simp [List.cons_lt_cons_iff]
    · simp only [tA, GeAll, List.cons_append, List.nil_append]
      exact ⟨cons_le_of_lt _ _ _ _ (by decide),
        cons_le_of_lt _ _ _ _ (by decide), trivial⟩
  have hh : entry S S.length = 2 :=
    entry_last S (Y ++ tA 0 ++ tA k ++ [0]) 2 (by simp [S, tA_succ])
  have hm3 : mbp S (Y.length + 1) = Y.length + 5 := by
    refine mbp_dec S Y [0,1,2,0] (2 :: copies [0,2] (k+1)) 1 2
      (Y.length + 1) (Y.length + 5) (by simp [S, tA, copies]) rfl (by simp) (by simp) hh
      (by decide) ?_
    rw [tailsLe_append]
    constructor
    · simp only [TailsLe, List.cons_append, List.nil_append, List.append_nil]
      refine ⟨fun _ => cons_le_of_lt _ _ _ _ (by decide),
        fun _ => ?_, fun _ => by omega, fun _ => cons_le_of_lt _ _ _ _ (by decide), trivial⟩
      rw [copies_succ]
      simp only [List.cons_append, List.nil_append]
      exact cons_le_cons_same 2 _ _ (cons_le_cons_same 0 _ _
        (cons_le_of_lt _ _ _ _ (by decide)))
    · simpa [TailsLe] using tailsLe_copies_02_end (k+1) 0
  have hf3 : fbp S 3 = Y.length + 5 := by simp [fbp, hp3, hm3]
  have he0 : entry S (Y.length + 4) = 0 :=
    entry_at S (Y ++ tA 0) (tA (k+1)) 0 _ (by simp [S])
      (by simp [tA, copies]) (by simp [tA])
  have he1 : entry S (Y.length + 1) = 0 :=
    entry_at S Y (tA 0 ++ tA (k+1)) 0 _ (by simp [S]) rfl (by simp [tA])
  have hbr3 : br S = 3 := by
    apply br_eq_three S (by simp [S, tA, copies_length]; omega) hnb2'
    apply breakAt_of_low S 3 (Y.length + 4) (by rw [hp3]; omega) (by rw [hf3]; omega)
    rw [hp3, he0, he1]
  exact ⟨hbr3, by rw [cut, hbr3, hf3]⟩

theorem br_A0_A_succ (Y : List ℕ) (k : ℕ) :
    br (Y ++ tA 0 ++ tA (k+1)) = 3 :=
  (break_and_cut_A0_A_succ Y k).1

theorem cut_A0_A_succ (Y : List ℕ) (k : ℕ) :
    cut (Y ++ tA 0 ++ tA (k+1)) = Y.length + 5 :=
  (break_and_cut_A0_A_succ Y k).2

/-- Adjacent `A0 A_(k+1)` has a prefix-independent cut. -/
theorem cut_prefix_A0_A_succ (Z : List ℕ) (k : ℕ) :
    cut (Z ++ tA 0 ++ tA (k+1)) =
      Z.length + cut (tA 0 ++ tA (k+1)) := by
  have h₂ : cut (tA 0 ++ tA (k+1)) = 5 := by
    simpa using cut_A0_A_succ [] k
  rw [cut_A0_A_succ Z k, h₂]

theorem fs_prefix_of_cut_shift (Z U : List ℕ) (a n : ℕ)
    (hc : cut (Z ++ U ++ [a + 1]) = Z.length + cut (U ++ [a + 1])) :
    fs (Z ++ U ++ [a + 1]) n = Z ++ fs (U ++ [a + 1]) n := by
  have hc' : cut (Z ++ (U ++ [a + 1])) = Z.length + cut (U ++ [a + 1]) := by
    simpa only [List.append_assoc] using hc
  simp [fs, good, bad, entry, hc', List.take_append, List.drop_append,
    List.dropLast_append_of_ne_nil, List.append_assoc, List.take_of_length_le,
    List.drop_eq_nil_of_le]

theorem fs_prefix_final_E_D_run (Z U : List ℕ) (m n : ℕ) :
    fs (Z ++ tA 0 ++ U ++ tE ++ copies [0,2] (m+1)) n =
      Z ++ fs (tA 0 ++ U ++ tE ++ copies [0,2] (m+1)) n := by
  have hc : cut (Z ++ (tA 0 ++ U ++ tE ++ copies [0,2] m ++ [0]) ++ [2]) =
      Z.length + cut ((tA 0 ++ U ++ tE ++ copies [0,2] m ++ [0]) ++ [2]) := by
    simpa [copies_succ', List.append_assoc] using cut_prefix_final_E_D_run Z U m
  have h := fs_prefix_of_cut_shift Z
    (tA 0 ++ U ++ tE ++ copies [0,2] m ++ [0]) 1 n hc
  simpa [copies_succ', List.append_assoc] using h

theorem fs_prefix_A0_W_D_run (Z : List ℕ) (m n : ℕ) :
    fs (Z ++ tA 0 ++ tW ++ copies [0,2] (m+1)) n =
      Z ++ fs (tA 0 ++ tW ++ copies [0,2] (m+1)) n := by
  have hc : cut (Z ++ (tA 0 ++ tW ++ copies [0,2] m ++ [0]) ++ [2]) =
      Z.length + cut ((tA 0 ++ tW ++ copies [0,2] m ++ [0]) ++ [2]) := by
    simpa [copies_succ', List.append_assoc] using cut_prefix_A0_W_D_run Z m
  have h := fs_prefix_of_cut_shift Z (tA 0 ++ tW ++ copies [0,2] m ++ [0]) 1 n hc
  simpa [copies_succ', List.append_assoc] using h

theorem fs_prefix_word_break_two (Z : List ℕ) (w : List PrefixTok) (hw : w ≠ [])
    (hb2 : breakAt (tA 0 ++ PrefixTok.rawWord w) 2) (n : ℕ) :
    fs (Z ++ tA 0 ++ PrefixTok.rawWord w) n =
      Z ++ fs (tA 0 ++ PrefixTok.rawWord w) n := by
  obtain ⟨u, a, hraw⟩ := rawWord_ends_positive w hw
  have hc := cut_prefix_word_break_two Z w hw hb2
  have h := fs_prefix_of_cut_shift Z (tA 0 ++ u) a n (by
    simpa [hraw, List.append_assoc] using hc)
  simpa [hraw, List.append_assoc] using h

theorem fs_prefix_word_break_three (Z : List ℕ) (w : List PrefixTok) (hw : w ≠ [])
    (hnot2 : ¬breakAt (tA 0 ++ PrefixTok.rawWord w) 2)
    (hbreak3 : breakAt (tA 0 ++ PrefixTok.rawWord w) 3)
    (hhead2 : 1 < p (tA 0 ++ PrefixTok.rawWord w) 2 ∧
      suf (tA 0 ++ PrefixTok.rawWord w) 1 <
        suf (tA 0 ++ PrefixTok.rawWord w) (p (tA 0 ++ PrefixTok.rawWord w) 2))
    (n : ℕ) :
    fs (Z ++ tA 0 ++ PrefixTok.rawWord w) n =
      Z ++ fs (tA 0 ++ PrefixTok.rawWord w) n := by
  obtain ⟨u, a, hraw⟩ := rawWord_ends_positive w hw
  have hc := cut_prefix_word_break_three Z w hw hnot2 hbreak3 hhead2
  have h := fs_prefix_of_cut_shift Z (tA 0 ++ u) a n (by
    simpa [hraw, List.append_assoc] using hc)
  simpa [hraw, List.append_assoc] using h

/-- Every word starting in a non-`D` token and ending in a positive-depth `A` is prefix independent. -/
theorem fs_prefix_final_A_succ (Z : List ℕ) (t : PrefixTok)
    (w : List PrefixTok) (k n : ℕ) (ht : t ≠ .D) :
    fs (Z ++ tA 0 ++ PrefixTok.rawWord (t :: w) ++ tA (k+1)) n =
      Z ++ fs (tA 0 ++ PrefixTok.rawWord (t :: w) ++ tA (k+1)) n := by
  let v := (t :: w) ++ [.A (k+1)]
  have hv : v ≠ [] := by simp [v]
  have hraw : PrefixTok.rawWord v = PrefixTok.rawWord (t :: w) ++ tA (k+1) := by
    change PrefixTok.rawWord ((t :: w) ++ [.A (k+1)]) = _
    rw [rawWord_append, rawWord_singleton]
    rfl
  have hnot2 : ¬breakAt (tA 0 ++ PrefixTok.rawWord v) 2 := by
    simpa [hraw, List.append_assoc] using
      (stage2_A (tA 0 ++ PrefixTok.rawWord (t :: w)) k).2.2
  have hb3 : breakAt (tA 0 ++ PrefixTok.rawWord v) 3 := by
    simpa [hraw, List.append_assoc] using breakAt_three_final_A_succ t w ht k
  have hh : 1 < p (tA 0 ++ PrefixTok.rawWord v) 2 ∧
      suf (tA 0 ++ PrefixTok.rawWord v) 1 <
        suf (tA 0 ++ PrefixTok.rawWord v) (p (tA 0 ++ PrefixTok.rawWord v) 2) := by
    simpa [hraw, List.append_assoc] using head_lt_parent_two_final_A_succ t w ht k
  simpa [hraw, List.append_assoc] using fs_prefix_word_break_three Z v hv hnot2 hb3 hh n

/-- Every final `W`, after any token prefix, has the prefix law. -/
theorem fs_prefix_final_W (Z : List ℕ) (v : List PrefixTok) (n : ℕ) :
    fs (Z ++ tA 0 ++ PrefixTok.rawWord v ++ tW) n =
      Z ++ fs (tA 0 ++ PrefixTok.rawWord v ++ tW) n := by
  let w := v ++ [.W]
  have hw : w ≠ [] := by simp [w]
  have hraw : PrefixTok.rawWord w = PrefixTok.rawWord v ++ tW := by
    change PrefixTok.rawWord (v ++ [.W]) = _
    rw [rawWord_append, rawWord_singleton]
    rfl
  have hb : breakAt (tA 0 ++ PrefixTok.rawWord w) 2 := by
    simpa [hraw, List.append_assoc] using breakAt_two_final_W v
  simpa [hraw, List.append_assoc] using fs_prefix_word_break_two Z w hw hb n

/-- A final `W D^(m+1)` also has the prefix law after every token prefix. -/
theorem fs_prefix_final_W_D_run (Z : List ℕ) (v : List PrefixTok) (m n : ℕ) :
    fs (Z ++ tA 0 ++ PrefixTok.rawWord v ++ tW ++ copies [0,2] (m+1)) n =
      Z ++ fs (tA 0 ++ PrefixTok.rawWord v ++ tW ++ copies [0,2] (m+1)) n := by
  let w := (v ++ [.W]) ++ List.replicate (m+1) PrefixTok.D
  have hw : w ≠ [] := by simp [w]
  have hraw : PrefixTok.rawWord w =
      PrefixTok.rawWord v ++ tW ++ copies [0,2] (m+1) := by
    change PrefixTok.rawWord ((v ++ [.W]) ++ List.replicate (m+1) .D) = _
    rw [rawWord_append, rawWord_append, rawWord_singleton, rawWord_replicate_D]
    rfl
  have hb3 : breakAt (tA 0 ++ PrefixTok.rawWord w) 3 := by
    simpa [hraw, List.append_assoc] using breakAt_three_final_W_D_run v m
  have hU : PrefixTok.rawWord v = [] ∨ ∃ V, PrefixTok.rawWord v = 0 :: V := by
    by_cases hv : v = []
    · left; simp [hv, PrefixTok.rawWord]
    · right; exact rawWord_starts_zero v hv
  have hh : 1 < p (tA 0 ++ PrefixTok.rawWord w) 2 ∧
      suf (tA 0 ++ PrefixTok.rawWord w) 1 <
        suf (tA 0 ++ PrefixTok.rawWord w) (p (tA 0 ++ PrefixTok.rawWord w) 2) := by
    simpa [hraw, List.append_assoc] using
      head_lt_parent_two_final_W_D_run (PrefixTok.rawWord v) m hU
  by_cases hb2 : breakAt (tA 0 ++ PrefixTok.rawWord w) 2
  · simpa [hraw, List.append_assoc] using fs_prefix_word_break_two Z w hw hb2 n
  · simpa [hraw, List.append_assoc] using fs_prefix_word_break_three Z w hw hb2 hb3 hh n

/-- The local search certificate gives prefix independence of `fs`. -/
theorem fs_prefix_of_local_certificate (Z U : List ℕ) (a n b : ℕ)
    (hb : 1 < b) (hbL : b ≤ (U ++ [a+1]).length)
    (hbreak : breakAt (U ++ [a+1]) b)
    (hno : ∀ i, 1 < i → i < b → ¬breakAt (U ++ [a+1]) i)
    (hc : ∀ j < b, ∃ r, 1 ≤ r ∧ r < p (U ++ [a+1]) j ∧
      suf (U ++ [a+1]) r < suf (U ++ [a+1]) (p (U ++ [a+1]) j) ∧
      sp (U ++ [a+1]) (p (U ++ [a+1]) j) = r) :
    fs (Z ++ U ++ [a+1]) n = Z ++ fs (U ++ [a+1]) n := by
  apply fs_prefix_of_cut_shift Z U a n
  simpa only [List.append_assoc] using
    cut_prefix_of_local_certificate Z (U ++ [a+1]) b
      (by simp) hb hbL hbreak hno hc

theorem fs_prefix_of_head_dominance (Z U : List ℕ) (a n b : ℕ)
    (hb : 1 < b) (hbL : b ≤ (U ++ [a+1]).length)
    (hbreak : breakAt (U ++ [a+1]) b)
    (hno : ∀ i, 1 < i → i < b → ¬breakAt (U ++ [a+1]) i)
    (hhead : ∀ j < b, 1 < p (U ++ [a+1]) j ∧
      suf (U ++ [a+1]) 1 < suf (U ++ [a+1]) (p (U ++ [a+1]) j)) :
    fs (Z ++ U ++ [a+1]) n = Z ++ fs (U ++ [a+1]) n := by
  apply fs_prefix_of_cut_shift Z U a n
  simpa only [List.append_assoc] using
    cut_prefix_of_head_dominance Z (U ++ [a+1]) b
      (by simp) hb hbL hbreak hno hhead

/-- Prefix independence when the token word ends in `A0`. -/
theorem fs_prefix_last_A0 (Z U : List ℕ) (n : ℕ) :
    fs (Z ++ [0,1,2] ++ U ++ tA 0) n =
      Z ++ fs ([0,1,2] ++ U ++ tA 0) n := by
  have h₁ := fs_A0 (Z ++ [0,1,2] ++ U) n
  have h₂ := fs_A0 ([0,1,2] ++ U) n
  change fs (Z ++ [0,1,2] ++ U ++ [0,1,2]) n =
    Z ++ fs ([0,1,2] ++ U ++ [0,1,2]) n
  rw [h₁, h₂]
  simp [List.append_assoc]

/-- Prefix independence when the token word ends in `E`. -/
theorem fs_prefix_last_E (Z U : List ℕ) (n : ℕ) :
    fs (Z ++ [0,1,2] ++ U ++ tE) n =
      Z ++ fs ([0,1,2] ++ U ++ tE) n := by
  have h₁ := fs_E (Z ++ [0,1,2] ++ U) n
  have h₂ := fs_E ([0,1,2] ++ U) n
  rw [h₁, h₂]
  simp [List.append_assoc]

/-- Prefix independence for a nonempty run of `W` after `A0`. -/
theorem fs_prefix_W_run (Z : List ℕ) (m n : ℕ) :
    fs (Z ++ tA 0 ++ copies tW (m+1)) n =
      Z ++ fs (tA 0 ++ copies tW (m+1)) n := by
  have h₁ := (law_W_A0 Z m).2.2.2 n
  have h₂ := (law_W_A0 [] m).2.2.2 n
  rw [copies_succ']
  simp only [List.nil_append] at h₂
  simp only [List.append_assoc] at h₁ h₂ ⊢
  rw [h₁, h₂]

/-- Prefix independence for adjacent `A0 A_(k+1)`. -/
theorem fs_prefix_A0_A_succ (Z : List ℕ) (k n : ℕ) :
    fs (Z ++ tA 0 ++ tA (k+1)) n =
      Z ++ fs (tA 0 ++ tA (k+1)) n := by
  have hc : cut (Z ++ (tA 0 ++ tA k ++ [0]) ++ [2]) =
      Z.length + cut ((tA 0 ++ tA k ++ [0]) ++ [2]) := by
    simpa [tA_succ, List.append_assoc] using cut_prefix_A0_A_succ Z k
  have h := fs_prefix_of_cut_shift Z (tA 0 ++ tA k ++ [0]) 1 n hc
  simpa [tA_succ, List.append_assoc] using h

theorem tA_append_D_copies (k r : ℕ) :
    tA k ++ copies [0,2] r = tA (k+r) := by
  simp [tA, copies_add]

/-- One `A` token followed by any `D` run has the prefix law. -/
theorem fs_prefix_A_D_run (Z : List ℕ) (k r n : ℕ) :
    fs (Z ++ tA 0 ++ tA k ++ copies [0,2] r) n =
      Z ++ fs (tA 0 ++ tA k ++ copies [0,2] r) n := by
  simp only [List.append_assoc]
  rw [tA_append_D_copies]
  cases h : k+r with
  | zero =>
      simpa [h, tA, copies, List.append_assoc] using fs_prefix_last_A0 Z [] n
  | succ q =>
      simpa [h, List.append_assoc] using fs_prefix_A0_A_succ Z q n

/-- The full first-unit case, including a trailing run of `D`. -/
theorem fs_prefix_single_unit_D_run (Z : List ℕ) (t : PrefixTok) (r n : ℕ)
    (ht : t ≠ .D) :
    fs (Z ++ tA 0 ++ t.raw ++ copies [0,2] r) n =
      Z ++ fs (tA 0 ++ t.raw ++ copies [0,2] r) n := by
  cases t with
  | D => exact False.elim (ht rfl)
  | A k => simpa [PrefixTok.raw] using fs_prefix_A_D_run Z k r n
  | W =>
      cases r with
      | zero =>
          simpa [PrefixTok.raw, copies, List.append_assoc] using fs_prefix_W_run Z 0 n
      | succ r =>
          simpa [PrefixTok.raw, List.append_assoc] using fs_prefix_A0_W_D_run Z r n
  | E =>
      cases r with
      | zero =>
          simpa [PrefixTok.raw, copies, tA, List.append_assoc] using
            fs_prefix_last_E Z [] n
      | succ r =>
          simpa [PrefixTok.raw, List.append_assoc] using
            fs_prefix_final_E_D_run Z [] r n

/-- Prefix independence when the final unit is `A_(k+1) W^(m+1)`. -/
theorem fs_prefix_last_AW (Z U : List ℕ) (k m n : ℕ) :
    fs (Z ++ [0,1,2] ++ U ++ tA (k+1) ++ copies tW (m+1)) n =
      Z ++ fs ([0,1,2] ++ U ++ tA (k+1) ++ copies tW (m+1)) n := by
  have h₁ := (law_W_A (Z ++ [0,1,2] ++ U) k m).2.2.2 n
  have h₂ := (law_W_A ([0,1,2] ++ U) k m).2.2.2 n
  rw [copies_succ']
  simp only [List.append_assoc] at h₁ h₂ ⊢
  rw [h₁, h₂]

/-- Prefix independence when the final unit is `E W^(m+1)`. -/
theorem fs_prefix_last_EW (Z U : List ℕ) (m n : ℕ) :
    fs (Z ++ [0,1,2] ++ U ++ tE ++ copies tW (m+1)) n =
      Z ++ fs ([0,1,2] ++ U ++ tE ++ copies tW (m+1)) n := by
  have h₁ := (law_W_E (Z ++ [0,1,2] ++ U) m).2.2.2 n
  have h₂ := (law_W_E ([0,1,2] ++ U) m).2.2.2 n
  rw [copies_succ']
  simp only [List.append_assoc] at h₁ h₂ ⊢
  rw [h₁, h₂]

/-- The full one-token case of prefix independence. -/
theorem fs_prefix_single (Z : List ℕ) (t : PrefixTok) (n : ℕ)
    (ht : t ≠ .D) :
    fs (Z ++ tA 0 ++ t.raw) n = Z ++ fs (tA 0 ++ t.raw) n := by
  cases t with
  | D => exact False.elim (ht rfl)
  | E => simpa [PrefixTok.raw, tA, copies] using fs_prefix_last_E Z [] n
  | W => simpa [PrefixTok.raw, copies] using fs_prefix_W_run Z 0 n
  | A k =>
      cases k with
      | zero =>
          simpa [PrefixTok.raw, tA, copies] using fs_prefix_last_A0 Z [] n
      | succ k =>
          simpa [PrefixTok.raw] using fs_prefix_A0_A_succ Z k n

/-- At any depth, an `E` terminal has the same prefix law. -/
theorem fs_prefix_depth_E (Z U : List ℕ) (d n : ℕ) :
    fs (Z ++ tA d ++ U ++ tE) n =
      Z ++ fs (tA d ++ U ++ tE) n := by
  have h₁ := fs_E (Z ++ tA d ++ U) n
  have h₂ := fs_E (tA d ++ U) n
  rw [h₁, h₂]
  simp [List.append_assoc]

/-- A nonempty `W` run immediately after `A_(d+1)` is prefix independent. -/
theorem fs_prefix_depth_W_run (Z : List ℕ) (d m n : ℕ) :
    fs (Z ++ tA (d+1) ++ copies tW (m+1)) n =
      Z ++ fs (tA (d+1) ++ copies tW (m+1)) n := by
  have h₁ := (law_W_A Z d m).2.2.2 n
  have h₂ := (law_W_A [] d m).2.2.2 n
  rw [copies_succ']
  simp only [List.nil_append, List.append_assoc] at h₁ h₂ ⊢
  rw [h₁, h₂]

/-- An `A_(k+1)` after a nonempty `W` run is prefix independent when `d ≤ k`. -/
theorem fs_prefix_depth_WA (Z : List ℕ) (d k m n : ℕ) (hd : d ≤ k) :
    fs (Z ++ tA d ++ copies tW (m+1) ++ tA (k+1)) n =
      Z ++ fs (tA d ++ copies tW (m+1) ++ tA (k+1)) n := by
  have h₁ := (law_A_adjacent Z d k m hd).2.2 n
  have h₂ := (law_A_adjacent [] d k m hd).2.2 n
  simp only [List.nil_append, List.append_assoc] at h₁ h₂ ⊢
  rw [h₁, h₂]

/-- Prefix independence for every token word whose first token is not `D`. -/
theorem fs_prefix_token_word (Z : List ℕ) (t : PrefixTok) (w : List PrefixTok)
    (ht : t ≠ .D) (n : ℕ) :
    fs (Z ++ tA 0 ++ PrefixTok.rawWord (t :: w)) n =
      Z ++ fs (tA 0 ++ PrefixTok.rawWord (t :: w)) n := by
  obtain ⟨u, x, r, hword, hx⟩ := word_trailing_D_decomp t w ht
  have hraw : PrefixTok.rawWord (t :: w) =
      PrefixTok.rawWord u ++ x.raw ++ copies [0,2] r := by
    rw [hword, rawWord_append, rawWord_append, rawWord_singleton, rawWord_replicate_D]
  rw [hraw]
  cases x with
  | D => exact False.elim (hx rfl)
  | A k =>
      simp only [PrefixTok.raw, List.append_assoc]
      rw [tA_append_D_copies]
      cases hkr : k+r with
      | zero =>
          simpa [hkr, tA, copies, List.append_assoc] using
            fs_prefix_last_A0 Z (PrefixTok.rawWord u) n
      | succ j =>
          cases u with
          | nil =>
              simpa [hkr, PrefixTok.rawWord, List.append_assoc] using
                fs_prefix_A0_A_succ Z j n
          | cons y ys =>
              have hy : y = t := by
                have h := congrArg List.head? hword
                simp at h
                exact h.symm
              subst y
              simpa [hkr, List.append_assoc] using
                fs_prefix_final_A_succ Z t ys j n ht
  | W =>
      cases r with
      | zero =>
          simpa [PrefixTok.raw, copies, List.append_assoc] using
            fs_prefix_final_W Z u n
      | succ m =>
          simpa [PrefixTok.raw, List.append_assoc] using
            fs_prefix_final_W_D_run Z u m n
  | E =>
      cases r with
      | zero =>
          simpa [PrefixTok.raw, copies, tA, List.append_assoc] using
            fs_prefix_last_E Z (PrefixTok.rawWord u) n
      | succ m =>
          simpa [PrefixTok.raw, List.append_assoc] using
            fs_prefix_final_E_D_run Z (PrefixTok.rawWord u) m n

/-- The zero-th expansion exposes the retained prefix and therefore the cut. -/
theorem cut_prefix_of_fs_zero (Z T : List ℕ) (hT : T ≠ [])
    (hpos : entry T T.length ≠ 0)
    (hfs : fs (Z ++ T) 0 = Z ++ fs T 0) :
    cut (Z ++ T) = Z.length + cut T := by
  have hlen : 1 ≤ T.length := List.length_pos_iff.mpr hT
  have hentry : entry (Z ++ T) (Z ++ T).length = entry T T.length := by
    simpa [List.length_append] using entry_prefix_shift Z T T.length hlen le_rfl
  have hT0 : fs T 0 = T.take (cut T) := by
    simp [fs, good, hT, hpos]
  have hpos' : entry (Z ++ T) (Z.length + T.length) ≠ 0 := by
    simpa [List.length_append] using (by rw [hentry]; exact hpos :
      entry (Z ++ T) (Z ++ T).length ≠ 0)
  have hZT0 : fs (Z ++ T) 0 = (Z ++ T).take (cut (Z ++ T)) := by
    simp [fs, good, hT, hpos']
  rw [hT0, hZT0] at hfs
  have h := congrArg List.length hfs
  have hcutT := cut_le_length T
  have hcutZT := cut_le_length (Z ++ T)
  have hcutZT' : cut (Z ++ T) ≤ Z.length + T.length := by simpa using hcutZT
  simp [List.length_take, hcutT, hcutZT'] at h
  omega

theorem cut_prefix_token_word (Z : List ℕ) (t : PrefixTok) (w : List PrefixTok)
    (ht : t ≠ .D) :
    cut (Z ++ tA 0 ++ PrefixTok.rawWord (t :: w)) =
      Z.length + cut (tA 0 ++ PrefixTok.rawWord (t :: w)) := by
  let T := tA 0 ++ PrefixTok.rawWord (t :: w)
  have hT : T ≠ [] := by simp [T, tA]
  obtain ⟨u, a, hraw⟩ := rawWord_ends_positive (t :: w) (by simp)
  have hpos : entry T T.length ≠ 0 := by
    have h := entry_last T (tA 0 ++ u) (a+1) (by simp [T, hraw, List.append_assoc])
    omega
  have hf : fs (Z ++ T) 0 = Z ++ fs T 0 := by
    simpa [T, List.append_assoc] using fs_prefix_token_word Z t w ht 0
  have hc := cut_prefix_of_fs_zero Z T hT hpos hf
  simpa [T, List.append_assoc] using hc

/-- The first break is at stage two or three; stage three has a strict head predecessor. -/
theorem token_word_break_shape (t : PrefixTok) (w : List PrefixTok) (ht : t ≠ .D) :
    let T := tA 0 ++ PrefixTok.rawWord (t :: w)
    br T = 2 ∨
      (br T = 3 ∧ 1 < p T 2 ∧ suf T 1 < suf T (p T 2)) := by
  obtain ⟨u, x, r, hword, hx⟩ := word_trailing_D_decomp t w ht
  have hraw : PrefixTok.rawWord (t :: w) =
      PrefixTok.rawWord u ++ x.raw ++ copies [0,2] r := by
    rw [hword, rawWord_append, rawWord_append, rawWord_singleton, rawWord_replicate_D]
  simp only [hraw]
  cases x with
  | D => exact False.elim (hx rfl)
  | A k =>
      simp only [PrefixTok.raw, List.append_assoc]
      rw [tA_append_D_copies]
      cases hkr : k+r with
      | zero =>
          left
          simpa [hkr, tA, copies, List.append_assoc] using
            (cut_A0 (tA 0 ++ PrefixTok.rawWord u)).2.2.1
      | succ j =>
          cases u with
          | nil =>
              right
              refine ⟨?_, ?_⟩
              · simpa [hkr, PrefixTok.rawWord, List.append_assoc] using
                  br_A0_A_succ [] j
              · simpa [hkr, PrefixTok.rawWord, List.append_assoc] using
                  head_lt_parent_two_A0_A_succ j
          | cons y ys =>
              have hy : y = t := by
                have h := congrArg List.head? hword
                simp at h
                exact h.symm
              subst y
              right
              have hb3 : breakAt (tA 0 ++ PrefixTok.rawWord (t :: ys) ++ tA (j+1)) 3 :=
                breakAt_three_final_A_succ t ys ht j
              refine ⟨?_, ?_⟩
              · simpa [hkr, List.append_assoc] using
                  br_final_A_succ (tA 0 ++ PrefixTok.rawWord (t :: ys)) j
                    (by simpa [List.append_assoc] using hb3)
              · simpa [hkr, List.append_assoc] using
                  head_lt_parent_two_final_A_succ t ys ht j
  | W =>
      cases r with
      | zero =>
          left
          have hb := breakAt_two_final_W u
          simpa [PrefixTok.raw, copies, List.append_assoc] using
            br_eq_two_of_breakAt (tA 0 ++ PrefixTok.rawWord u ++ tW)
              (by simp [tA, tW, copies]) hb
      | succ m =>
          have hU : PrefixTok.rawWord u = [] ∨ ∃ V, PrefixTok.rawWord u = 0 :: V := by
            by_cases hu : u = []
            · left; simp [hu, PrefixTok.rawWord]
            · right; exact rawWord_starts_zero u hu
          rcases br_final_W_D_run u m with hb2 | hb3
          · left
            simpa [PrefixTok.raw, List.append_assoc] using hb2
          · right
            refine ⟨?_, ?_⟩
            · simpa [PrefixTok.raw, List.append_assoc] using hb3
            · simpa [PrefixTok.raw, List.append_assoc] using
                head_lt_parent_two_final_W_D_run (PrefixTok.rawWord u) m hU
  | E =>
      left
      cases r with
      | zero =>
          simpa [PrefixTok.raw, copies, List.append_assoc] using
            (cut_E (tA 0 ++ PrefixTok.rawWord u)).2.2.1
      | succ m =>
          simpa [PrefixTok.raw, List.append_assoc] using
            br_final_E_D_run (tA 0 ++ PrefixTok.rawWord u) m

/-- Universal local certificate for the `A0` token language. -/
theorem token_word_head_certificate (t : PrefixTok) (w : List PrefixTok)
    (ht : t ≠ .D) :
    let T := tA 0 ++ PrefixTok.rawWord (t :: w)
    (br T = 2 ∨ br T = 3) ∧
      ∀ j < br T, 1 < p T j ∧ suf T 1 < suf T (p T j) := by
  let T := tA 0 ++ PrefixTok.rawWord (t :: w)
  have h0 : 1 < p T 0 ∧ suf T 1 < suf T (p T 0) := by
    simpa [T] using head_lt_parent_zero_word (t :: w) (by simp)
  have h1 : 1 < p T 1 ∧ suf T 1 < suf T (p T 1) := by
    simpa [T] using head_lt_parent_one_word (t :: w) (by simp)
  rcases token_word_break_shape t w ht with hb2 | ⟨hb3, h2⟩
  · constructor
    · exact Or.inl hb2
    · intro j hj
      rw [hb2] at hj
      have hj' : j = 0 ∨ j = 1 := by omega
      rcases hj' with rfl | rfl
      · exact h0
      · exact h1
  · constructor
    · exact Or.inr hb3
    · intro j hj
      rw [hb3] at hj
      have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hj' with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2

end SSOS.Seq
