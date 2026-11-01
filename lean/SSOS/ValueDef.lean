import SSOS.VNote

/-!
# The conjectural valuation `o` below ζ₀ (ported from `work/token_value.py`)

This file transcribes the Python evaluator `token_value.value` under the
canonical settings

* `token_value.P1_ROOT_EXPERIMENT = True`, `token_value.P1_V_BITS_EXPERIMENT = True`,
  every other `token_value` flag at its default (in particular `P2_V7_EXPERIMENT = False`);
* `token_tree.GENERAL_COPY_EXPERIMENT = V_ROOT_EXPERIMENT = V_BITS_EXPERIMENT = True`
  (the state `token_value` switches on), every other `token_tree` flag off.

Only the code paths reachable under these settings are ported.  A Python
`Unknown` exception is `none`.  No theorem about the map is claimed here: it is
a definition, reproducing the Python values (checked by `SSOS/ValueTest.lean`).

Termination: the arithmetic on notations recurses structurally (on a notation
or on a depth).  The recursions on sequences (units, `T`, `T2`, token parses,
the token loop, `value` on `s[:-1]`) carry an explicit fuel argument, started
at the length of the input plus one; every such recursion shortens its
sequence, so the fuel is never exhausted on a call made from `val`.
-/

namespace SSOS
namespace ValueDef

open VNote

/-! ## Sequences -/

/-- Python `l[-n:] == suf`. -/
def endsWith (l suf : List ℕ) : Bool :=
  decide (suf.length ≤ l.length) && l.drop (l.length - suf.length) == suf

/-- Python `l[:-n]` (note `l[:-0] == []`). -/
def pyDropRight {α : Type} (n : ℕ) (l : List α) : List α :=
  if n = 0 then [] else l.take (l.length - n)

/-- Python tuple order `l < m`. -/
def lexLt : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: l, b :: m => decide (a < b) || (decide (a = b) && lexLt l m)

/-- End of a `conj2.units` block starting at `i`, scanning from `j`. -/
def unitEnd (Y : List ℕ) (i : ℕ) : ℕ → ℕ → ℕ
  | 0, j => j
  | fuel + 1, j =>
    let n := Y.length
    let g := fun t => Y.getD t 0
    if j < n ∧ (g j ≠ 0 ∨ (j + 1 < n ∧ g (j + 1) ≠ 0 ∧ j > i ∧ g (j - 1) ≠ 0)) then
      unitEnd Y i fuel (j + 1)
    else j

def unitsAux (Y : List ℕ) : ℕ → ℕ → List (List ℕ)
  | 0, _ => []
  | fuel + 1, i =>
    if i < Y.length then
      if Y.getD i 0 = 0 then [0] :: unitsAux Y fuel (i + 1)
      else
        let j := unitEnd Y i (Y.length + 1) i
        ((Y.drop i).take (j - i)) :: unitsAux Y fuel j
    else []

/-- `conj2.units`: a 0 outside blocks, or a maximal block of nonzero entries
separated by single 0s. -/
def units (Y : List ℕ) : List (List ℕ) := unitsAux Y (Y.length + 1) 0

/-- `conj2.T`: in every run of nonzero entries, drop the first entry if the
run is all 1s. -/
def T (B : List ℕ) : List ℕ :=
  [0].intercalate ((B.splitOn 0).map fun r => if r ≠ [] ∧ r.all (· = 1) then r.tail else r)

/-- `v_bits43.T2`: drop the leading 2 of every run (`none` if a run is not led by 2). -/
def T2 (u : List ℕ) : Option (List ℕ) :=
  let runs := u.splitOn 0
  if runs.all (fun r => r.head? = some 2) then some ([0].intercalate (runs.map List.tail))
  else none

/-! ## Binary and 0/1/2 ranks -/

/-- `conj.v` on 0/1 words (also `token_tree.binary_index`, read as an ordinal).
On 0/1 words `conj.units`/`conj.T` agree with `conj2.units`/`conj2.T`. -/
def conjV : ℕ → List ℕ → VNote
  | 0, _ => zero
  | fuel + 1, y =>
    (units y).foldl (fun acc u =>
      add acc (if u = [0] then ONE else w (add ONE (conjV fuel (T u))))) zero

def binV (y : List ℕ) : VNote := conjV (y.length + 1) y

/-- `v_bits43.v2`. -/
def v2 : ℕ → List ℕ → Option VNote
  | 0, _ => none
  | fuel + 1, y =>
    (units y).foldlM (fun acc u =>
      if u = [0] then some (add acc ONE)
      else if u = [2] then some (add acc E0)
      else
        let t := T u
        if t = u then do
          let t2 ← T2 u
          let x ← v2 fuel t2
          pure (add acc (P ONE x))
        else do
          let x ← v2 fuel t
          pure (add acc (w (add ONE x)))) zero

/-! ## Tokens -/

inductive Tok where
  | W | D | V
  | A (k : ℕ)
  | E (k : ℕ)
  | L (k : ℕ)
  deriving DecidableEq, Repr, Inhabited

def Tok.isOp : Tok → Bool
  | .W | .D | .V => true
  | _ => false

def Tok.isA : Tok → Bool
  | .A _ => true
  | _ => false

def Tok.isE : Tok → Bool
  | .E _ => true
  | _ => false

/-- `v_bits43.bits`. -/
def vbits (copies : List Tok) : Option (List ℕ) :=
  copies.foldlM (fun out t =>
    match t with
    | .W => some (out ++ [0])
    | .D => some (out ++ [1])
    | .V => if out.getLast? = some 1 then some (out.dropLast ++ [2]) else some (out ++ [2])
    | _ => none) []

/-- `token_tree.copy_rank` (with `V_BITS`): W/D words by the binary rank,
words containing V by `v_bits43.rank`. -/
def copyRank (copies : List Tok) : Option VNote :=
  if Tok.V ∈ copies then do
    let b ← vbits copies
    v2 (b.length + 1) b
  else some (binV (copies.map fun t => if t = .W then 0 else 1))

/-- Strip leading `(0,2)` pairs: their number and the rest. -/
def countD : List ℕ → ℕ × List ℕ
  | 0 :: 2 :: r => let p := countD r; (p.1 + 1, p.2)
  | l => (0, l)

/-- One `A_k`/`W`/`E_k` token at the head of `l` (which starts with `0,1,2`). -/
def akToken (l : List ℕ) : Tok × List ℕ :=
  let p := countD (l.drop 3)
  match p.2 with
  | 1 :: r => (if p.1 = 0 then .W else .E p.1, r)
  | r => (.A p.1, r)

/-- `token_value.parse_tail`. -/
def parseTail : ℕ → List ℕ → Option (List Tok)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, l@(_ :: _) =>
    if l.take 3 = [0, 1, 2] then
      let p := akToken l
      (p.1 :: ·) <$> parseTail fuel p.2
    else none

/-- `token_tree.parse` (with `V_ROOT`). -/
def ttParse (allowD : Bool) : ℕ → List ℕ → Option (List Tok)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, l@(x :: rest) =>
    if allowD ∧ l.take 3 = [0, 2, 1] then (Tok.V :: ·) <$> ttParse allowD fuel (l.drop 3)
    else if allowD ∧ l.take 2 = [0, 2] then (Tok.D :: ·) <$> ttParse allowD fuel (l.drop 2)
    else if allowD ∧ x = 0 ∧ l.take 3 ≠ [0, 1, 2] then
      let j := 1 + (rest.takeWhile (· = 1)).length
      if j > 1 then (Tok.L (j - 1) :: ·) <$> ttParse allowD fuel (l.drop j)
      else (Tok.A 0 :: ·) <$> ttParse allowD fuel (l.drop 1)
    else if l.take 3 ≠ [0, 1, 2] then none
    else
      let p := akToken l
      (p.1 :: ·) <$> ttParse allowD fuel p.2

/-- `token_base2.parse`: `2` followed by `A=(0,1,2)` (bit 0) / `D=(0,2)` (bit 1). -/
def b2bits : List ℕ → Option (List ℕ)
  | [] => some []
  | 0 :: 1 :: 2 :: r => (0 :: ·) <$> b2bits r
  | 0 :: 2 :: r => (1 :: ·) <$> b2bits r
  | _ => none

def b2parse : List ℕ → Option (List ℕ)
  | 2 :: tail => b2bits tail
  | _ => none

/-! ## `token_value`: the 0/1/2 index fold on notations -/

/-- Number of trailing terms equal to `1`. -/
def countTrailOne (l : List (VNote × VNote)) : ℕ :=
  (l.reverse.takeWhile (fun t => t = (zero, zero))).length

def towerW (seed : VNote) : ℕ → VNote
  | 0 => seed
  | n + 1 => w (towerW seed n)

/-- `token_value.bump_last`. -/
def bumpLast : VNote → ℕ → VNote → Option VNote
  | idx, 0, amt => some (add idx amt)
  | idx, d + 1, amt =>
    let l := idx.toList
    match l.getLast? with
    | none => none
    | some (a, b) =>
      let exponent := if a = zero then b else single a b
      if exponent = zero then
        let n := countTrailOne l
        some (add (ofList (pyDropRight n l)) (towerW (add (nat n) amt) (d + 1)))
      else do
        let changed ← bumpLast exponent d amt
        pure (add (ofList l.dropLast) (w changed))

/-- `token_value.epsilon_iteration`. -/
def epsIterV : VNote → ℕ → ℕ → Option VNote
  | v, d + 1, m =>
    let l := v.toList
    match l.getLast? with
    | none => none
    | some (a, b) =>
      let exponent := if a = zero then b else single a b
      if exponent = zero then none
      else do
        let e ← epsIterV exponent d m
        pure (add (ofList l.dropLast) (w e))
  | v, 0, m =>
    let l := v.toList
    match l.getLast? with
    | none => none
    | some (a, b) =>
      match nextFp ONE (single a b) with
      | zero => none
      | cons _ q _ =>
        let q := if m = 0 then q else add q (w (nat m))
        some (add (ofList l.dropLast) (P ONE q))

/-- The token loop of `token_value.index`. -/
def indexLoop (base : VNote) (j : ℕ) :
    ℕ → List Tok → VNote → Bool → ℕ → Option VNote
  | _, [], value, _, _ => some value
  | 0, _ :: _, _, _, _ => none
  | fuel + 1, token :: rest, value, fresh, ad =>
    let m := (rest.takeWhile (· = .W)).length
    let rest' := rest.drop m
    let amount := w (nat m)
    match token with
    | .A k => do
      let v ←
        if k = 0 then some (add value amount)
        else if fresh then some (add base (towerW (if m = 0 then nat (j + 2) else amount) k))
        else bumpLast value k amount
      indexLoop base j fuel rest' v false k
    | .E 1 => do
      let v ←
        if fresh then some (add base (P ONE (if m = 0 then zero else amount)))
        else epsIterV value ad m
      indexLoop base j fuel rest' v false ad
    | _ => none

/-- `token_value.index`. -/
def index (tokens : List Tok) : Option VNote :=
  let j := (tokens.takeWhile (· = .W)).length
  let base := if j = 0 then E0 else P ONE (w (nat j))
  indexLoop base j (tokens.length + 1) (tokens.drop j) base true 0

/-! ## `token_tree`: CNF trees with copy frames -/

/-- `token_tree.Frame`, keeping only what the values depend on: whether the
copy word contains `D`, the covered depth, and the copy rank. -/
structure Frame where
  hasD : Bool
  covered : ℕ
  rank : Option VNote

/-- `token_tree.CNF`: `cons a b fr r` is the term φ(a, b) (carrying frame
`fr`) followed by `r`.  Origins do not affect values and are dropped. -/
inductive FT where
  | nil : FT
  | cons (a b : FT) (fr : Option Frame) (rest : FT) : FT
  deriving Inhabited

namespace FT

def ord : FT → VNote
  | nil => .zero
  | cons a b _ r => .cons (ord a) (ord b) (ord r)

def ofOrd : VNote → FT
  | .zero => nil
  | .cons a b r => cons (ofOrd a) (ofOrd b) none (ofOrd r)

def toList : FT → List (FT × FT × Option Frame)
  | nil => []
  | cons a b f r => (a, b, f) :: toList r

def ofListApp : List (FT × FT × Option Frame) → FT → FT
  | [], y => y
  | (a, b, f) :: l, y => cons a b f (ofListApp l y)

def ofList (l : List (FT × FT × Option Frame)) : FT := ofListApp l nil

def termOrd (t : FT × FT × Option Frame) : VNote := single (ord t.1) (ord t.2.1)

def phi (a b : FT) (fr : Option Frame) : FT :=
  match b with
  | cons c _ _ nil => if VNote.cmp (ord c) (ord a) = .gt then b else cons a b fr nil
  | _ => cons a b fr nil

def power (b : FT) (fr : Option Frame) : FT := phi nil b fr

def one : FT := power nil none

def natural (n : ℕ) : FT := ofList (List.replicate n (nil, nil, none))

def plus (a b : FT) : FT :=
  match b with
  | nil => a
  | cons c d _ _ =>
    let h := single (ord c) (ord d)
    ofListApp ((a.toList.reverse.dropWhile (fun t => VNote.cmp (termOrd t) h = .lt)).reverse) b

def successor (a : FT) : FT := plus a one

def omega : FT := power one none

def epsilon (b : FT) (fr : Option Frame) : FT := phi one b fr

def tower (seed : FT) (fr : Option Frame) : ℕ → FT
  | 0 => seed
  | n + 1 => power (tower seed fr n) fr

/-- Replace the frame of every top-level term. -/
def setFrame (fr : Option Frame) : FT → FT
  | nil => nil
  | cons a b _ r => cons a b fr (setFrame fr r)

/-- `token_tree.next_fixed`. -/
def nextFixed (level : FT) : FT → FT
  | nil => phi level nil none
  | x@(cons a b _ _) =>
    if VNote.cmp (ord x) (ord (phi level nil none)) = .lt then phi level nil none
    else match VNote.cmp (ord a) (ord level) with
      | .eq => phi level (successor b) none
      | .gt => phi level (successor x) none
      | .lt => nextFixed level b

/-- `token_tree.bump` (`req` is the requested depth of the outer call). -/
def bump (tree : FT) (depth : ℕ) (amount : FT) (req : ℕ) : Option FT :=
  match depth with
  | 0 => some (plus tree amount)
  | d + 1 =>
    let l := tree.toList
    match l.getLast? with
    | none => none
    | some (ti, ta, tf) =>
      let pre := ofList l.dropLast
      let promoted : Option FT :=
        match tf with
        | some f =>
          if f.hasD && decide (req > f.covered) then
            let seed := plus ((f.rank.map ofOrd).getD omega) amount
            some (plus pre (tower seed (some { f with covered := req }) (d + 1)))
          else none
        | none => none
      match promoted with
      | some r => some r
      | none =>
        let exponent := match ti with
          | nil => ta
          | _ => cons ti ta tf nil
        match exponent with
        | nil =>
          let n := (l.reverse.takeWhile (fun t => termOrd t = VNote.ONE)).length
          let seed := plus (natural n) amount
          some (plus (ofList (pyDropRight n l)) (tower seed tf (d + 1)))
        | _ => do
          let changed ← bump exponent d amount req
          pure (plus pre (power changed tf))

/-- `token_tree.epsilon_iteration`. -/
def epsIter (tree : FT) (depth : ℕ) (iterated : Bool) (amount : FT) : Option FT :=
  match depth with
  | d + 1 =>
    let l := tree.toList
    match l.getLast? with
    | none => none
    | some (ti, ta, tf) =>
      let exponent := match ti with
        | nil => ta
        | _ => cons ti ta tf nil
      match exponent with
      | nil => none
      | _ => do
        let e ← epsIter exponent d iterated amount
        pure (plus (ofList l.dropLast) (power e none))
  | 0 =>
    let l := tree.toList
    match l.getLast? with
    | none => none
    | some (ti, ta, tf) =>
      match nextFixed one (cons ti ta tf nil) with
      | nil => none
      | cons _ q _ _ =>
        let q := if iterated then plus q amount else q
        some (plus (ofList l.dropLast) (epsilon q none))

end FT

open FT in
/-- The token loop of `token_tree.fold`. -/
def foldLoop (general : Bool) (base offset : FT) :
    ℕ → List Tok → FT → Bool → ℕ → Option FT
  | _, [], value, _, _ => some value
  | 0, _ :: _, _, _, _ => none
  | fuel + 1, token :: rest, value, fresh, ad =>
    if token.isOp then none
    else
      let m := (rest.takeWhile (· = .W)).length
      let r1 := rest.drop m
      let rankLimit := r1.head? = some Tok.D
      if rankLimit ∧ m = 0 ∧ ¬(general ∧ token.isE) then none
      else
        let copies1 := List.replicate m Tok.W ++ (if rankLimit then [Tok.D] else [])
        let r2 := if rankLimit then r1.drop 1 else r1
        let ex := if general then r2.takeWhile Tok.isOp else []
        let copies := copies1 ++ ex
        let r3 := r2.drop ex.length
        let k := match token with
          | .A k => k
          | .E k => k
          | _ => 0
        let rankO : Option (Option VNote) :=
          if general then (some <$> copyRank copies) else some none
        match rankO with
        | none => none
        | some rank =>
          let amount0 := power (if general then ofOrd (rank.getD .zero)
            else if rankLimit then omega else natural m) none
          let iterated := if general then copies ≠ [] else m ≠ 0
          let frame : Option Frame :=
            if iterated ∧ token.isA then some ⟨decide (Tok.D ∈ copies), k, rank⟩ else none
          let amount := match frame with
            | some _ => setFrame frame amount0
            | none => amount0
          let next : Option FT :=
            match token with
            | .A k =>
              if k = 0 then some (plus value amount)
              else if fresh then some (plus base (tower (plus offset amount) frame k))
              else bump value k amount k
            | .L n =>
              let v := plus value (ofOrd (binV (0 :: List.replicate n 1)))
              some (if copies ≠ [] ∨ rankLimit then plus v amount else v)
            | .E 1 =>
              if fresh ∧ general ∧ ¬iterated ∧ ¬ VNote.lt (ord offset) VNote.E0 then
                some (plus base (ofOrd (nextFp VNote.ONE (ord offset))))
              else if fresh then
                some (plus base (epsilon (if iterated then amount else nil) none))
              else epsIter value ad iterated amount
            | _ => none
          match next with
          | none => none
          | some v =>
            let ad' := match token with
              | .A k => k
              | _ => ad
            foldLoop general base offset fuel r3 v false ad'

open FT in
/-- `token_tree.fold` (TAIL_S / RELTAIL / movable-one / cut-copy paths are off). -/
def fold (tokens : List Tok) (boundary general : Bool) : Option FT := do
  let j :=
    if general then (tokens.takeWhile Tok.isOp).length
    else if !boundary then (tokens.takeWhile (· = .W)).length
    else 0
  let pre := tokens.take j
  let rootCopy :=
    if general then Tok.W :: pre
    else if boundary then [Tok.W, Tok.D]
    else List.replicate (j + 1) Tok.W
  let bo : FT × FT ←
    if general then do
      let rank ← copyRank pre
      let off ← copyRank rootCopy
      pure (if j ≠ 0 then epsilon (power (ofOrd rank) none) none else epsilon nil none, ofOrd off)
    else if boundary then pure (epsilon (power omega none) none, omega)
    else pure (epsilon (if j = 0 then nil else power (natural j) none) none, natural (j + 1))
  foldLoop general bo.1 bo.2 (tokens.length + 1) (tokens.drop j) bo.1 true 0

/-- `token_tree.known_block_tree`, read as an ordinal. -/
def knownBlock (u : List ℕ) : Option VNote :=
  match b2parse u with
  | some bits => some (P ONE (binV bits))
  | none =>
    if u = [2, 1, 0, 2] then some (P ONE (P ONE (w OMEGA)))
    else if u.take 4 = [2, 1, 0, 2] then do
      let toks ← ttParse true (u.length + 1) (u.drop 4)
      let f ← fold toks true false
      pure (P ONE f.ord)
    else if u.take 2 = [2, 1] then do
      let toks ← ttParse false (u.length + 1) (u.drop 2)
      let f ← fold toks false false
      pure (P ONE f.ord)
    else none

/-- `token_tree.block_value` (GENERAL_COPY on). -/
def ttBlock (u : List ℕ) : Option VNote :=
  match knownBlock u with
  | some v => some v
  | none =>
    if u.take 2 = [2, 1] then do
      let toks ← ttParse true (u.length + 1) (u.drop 2)
      let f ← fold toks false true
      pure (P ONE f.ord)
    else none

/-- The structural 0/1/2 body fold shared by `token_value.body_value` and
`token_tree.body_tree`, for a given block valuation. -/
def bodyGen (block : List ℕ → Option VNote) : ℕ → List ℕ → Option VNote
  | 0, _ => none
  | fuel + 1, body =>
    (units body).foldlM (fun acc u =>
      if u = [0] then some (add acc ONE)
      else if u = [2] then some (add acc E0)
      else
        let t := T u
        if t = u then (add acc ·) <$> block u
        else (fun x => add acc (w (add ONE x))) <$> bodyGen block fuel t) zero

def ttValueAux : ℕ → List ℕ → Option VNote
  | 0, _ => none
  | fuel + 1, s =>
    if s.take 2 ≠ [0, 0] ∨ s.any (· > 2) then none
    else if s.length > 2 ∧ s.getLast? = some 0 then succ <$> ttValueAux fuel s.dropLast
    else (add (nat 2) ·) <$> bodyGen ttBlock ((s.drop 2).length + 1) (s.drop 2)

/-- `token_tree.value`. -/
def ttValue (s : List ℕ) : Option VNote := ttValueAux (s.length + 1) s

/-! ## `token_value`: blocks, bodies and the value -/

/-- `token_value.p1_v_anchor()`.  In Python this is the stable sup of the four
samples `token_tree.value((0,0,2,1)+(0,2)*n)`, n = 1..4, found by
`evalord.sup`; its value is the constant `F(P V) = ε_ε_ε0`
(P = (0,0,2,1,0,2), V = (0,2,1)).  It is defined here as that constant. -/
def anchor : VNote := P ONE (P ONE (P ONE zero))

/-- Strip trailing `W = (0,1,2,1)` units: their number and the rest. -/
def stripW : ℕ → List ℕ → ℕ × List ℕ
  | 0, l => (0, l)
  | fuel + 1, l =>
    if endsWith l [0, 1, 2, 1] then
      let p := stripW fuel (l.take (l.length - 4))
      (p.1 + 1, p.2)
    else (0, l)

/-- The relative-tail loop of `token_value.block_value`: the base and the
amounts in the order Python appends them. -/
def relTails : ℕ → List ℕ → List VNote → List ℕ × List VNote
  | 0, base, amounts => (base, amounts)
  | fuel + 1, base, amounts =>
    if endsWith base [0, 1, 2, 0, 1, 2, 1, 0, 2] then
      relTails fuel (base.take (base.length - 9)) (amounts ++ [w OMEGA])
    else
      let p := stripW (base.length + 1) base
      if !endsWith p.2 [0, 1, 2] then (base, amounts)
      else relTails fuel (p.2.take (p.2.length - 3)) (amounts ++ [w (nat p.1)])

/-- `token_value.block_value` (P1_ROOT and P1_V_BITS on, P2_V7 off). -/
def tvBlockAux : ℕ → List ℕ → Option VNote
  | 0, _ => none
  | fuel + 1, u =>
    if u = [2, 1, 0, 2, 0, 2, 1] then some anchor
    else
      let p1 : Option VNote := if u.take 7 = [2, 1, 0, 2, 0, 2, 1] then ttBlock u else none
      match p1 with
      | some v => some v
      | none =>
        match b2parse u with
        | some bits => some (P ONE (binV bits))
        | none =>
          if u = [2, 1, 0, 2, 0, 1, 2, 0, 2] then do
            let x ← tvBlockAux fuel [2, 1, 0, 2]
            match x with
            | zero => none
            | cons _ alpha _ => pure (P ONE (add alpha (w (succ OMEGA))))
          else
            let rt := relTails (u.length + 1) u []
            let base := rt.1
            let amounts := rt.2
            -- `none`: Unknown raised; `some none`: fall through; `some (some v)`: return v
            let rel : Option (Option VNote) :=
              if amounts ≠ [] ∧ units base = [base] ∧ T base = base then
                match tvBlockAux fuel base with
                | none => none
                | some x =>
                  match x with
                  | cons a i zero =>
                    if a = ONE then some (some (P ONE (amounts.reverse.foldl add i)))
                    else some none
                  | _ => some none
              else some none
            match rel with
            | none => none
            | some (some v) => some v
            | some none =>
              if u.take 2 ≠ [2, 1] then none
              else if u = [2, 1, 0, 2] then some (P ONE (P ONE (w OMEGA)))
              else do
                let toks ← parseTail (u.length + 1) (u.drop 2)
                let i ← index toks
                pure (P ONE i)

def tvBlock (u : List ℕ) : Option VNote := tvBlockAux (u.length + 1) u

/-- `token_value.value` together with `p1_root_candidate`. -/
def valAux : ℕ → List ℕ → Option VNote
  | 0, _ => none
  | fuel + 1, s =>
    if s.take 2 ≠ [0, 0] ∨ s.any (· > 2) then none
    else if s.length > 2 ∧ s.getLast? = some 0 then succ <$> valAux fuel s.dropLast
    else
      match bodyGen tvBlock ((s.drop 2).length + 1) (s.drop 2) with
      | some v => some (add (nat 2) v)
      | none =>
        -- p1_root_candidate
        let root := [0, 0, 2, 1, 0, 2]
        let p1 := root ++ [1]
        let p2 := p1 ++ [1]
        if s.take 6 ≠ root then none
        else if !lexLt s p2 then none
        else if !lexLt s p1 then none
        else if s = root ++ [0, 2, 1] then some anchor
        else if s = root ++ [0, 2, 0, 1] then (fun x => w (succ x)) <$> valAux fuel (root ++ [0, 2])
        else if s = root ++ [0, 2, 1, 0, 1] then
          (fun x => w (succ x)) <$> valAux fuel (root ++ [0, 2, 1])
        else ttValue s

/-- The evaluator: `some v` is the Python `value(s)`, `none` is `Unknown`. -/
def val (S : List ℕ) : Option VNote := valAux (S.length + 1) S

end ValueDef

/-- The conjectural ordinal translation `o` of an SSOS sequence below ζ₀
(0 where the evaluator is undecided). -/
noncomputable def oVal (S : List ℕ) : Ordinal.{0} :=
  match ValueDef.val S with
  | some v => VNote.toOrd v
  | none => 0

end SSOS
