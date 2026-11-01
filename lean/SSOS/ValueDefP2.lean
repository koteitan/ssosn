import SSOS.ValueDef

/-!
# The valuation with the §44 P2 extension (ported from `work/token_value.py`)

This file transcribes the Python evaluator `token_value.value` under the
settings

* `token_value.P1_ROOT_EXPERIMENT = P1_V_BITS_EXPERIMENT = P2_V7_EXPERIMENT = True`,
  every other `token_value` flag at its default;
* `token_tree.GENERAL_COPY_EXPERIMENT = V_ROOT_EXPERIMENT = V_BITS_EXPERIMENT = True`
  (the state `token_value` switches on), with `token_tree.P2_V7_EXPERIMENT`
  on exactly where `token_value` switches it on (the root-V block fallback and
  `p1_root_candidate`), every other `token_tree` flag off;
* the v7 rank of `work/v_bits44.py` (`bits6`, `v4`, `v7`, `B7`).

It reuses `SSOS.ValueDef` (sequences, tokens, the CNF trees with frames, the
P2-off evaluator pieces) and leaves `SSOS.ValueDef.val` untouched.  A Python
`Unknown` is `none`.  No theorem about the map is claimed: it is a definition,
checked against Python by `SSOS/ValueTestP2.lean`.

Python caches (`lru_cache`) are shared between the P2-on and P2-off states of
`token_tree`; this port evaluates each call in the state Python sets for it.
The test data were generated in forward, reverse and per-case-fresh-cache
orders and agree, so the cache order does not affect the tested values.

Termination: as in `SSOS.ValueDef`, recursions on sequences carry fuel started
at the length of the input plus one, and every such recursion shortens its
sequence.  No new sampled-sup constant is introduced (the only one on the
reachable path is `ValueDef.anchor`, reused).
-/

namespace SSOS
namespace ValueDefP2

open VNote ValueDef

/-! ## `v_bits44`: the v4 fold and the v7 root rank -/

/-- `v_bits44.Tk`: drop the leading `k` of every run (all heads must be `k`). -/
def Tk (u : List ℕ) (k : ℕ) : Option (List ℕ) :=
  let runs := u.splitOn 0
  if 2 ≤ k ∧ runs.all (fun r => r.head? = some k) then
    some ([0].intercalate (runs.map List.tail))
  else none

/-- `v_bits44.Tstar_k`: drop the leading `k` only in runs headed `k`; every
head must be at least `k`. -/
def TstarK (u : List ℕ) (k : ℕ) : Option (List ℕ) :=
  let runs := u.splitOn 0
  if 2 ≤ k ∧ runs ≠ [] ∧ runs.all (fun r => match r.head? with
      | some h => decide (k ≤ h)
      | none => false) then
    some ([0].intercalate (runs.map fun r => if r.head? = some k then r.tail else r))
  else none

/-- `v_bits44.v4`. -/
def v4 : ℕ → List ℕ → Option VNote
  | 0, _ => none
  | fuel + 1, word =>
    (units word).foldlM (fun acc u =>
      if u = [0] then some (add acc ONE)
      else if u = [2] then some (add acc E0)
      else
        let t := T u
        if t ≠ u then (fun x => add acc (w (add ONE x))) <$> v4 fuel t
        else do
          let hs ← (u.splitOn 0).mapM List.head?
          let k0 ← hs.head?
          if hs.any (· < 2) then none
          else
            let k := hs.foldl min k0
            let reduced ← if hs.all (· = k) then Tk u k else TstarK u k
            let x ← v4 fuel reduced
            pure (add acc (P (nat (k - 1)) x))) zero

/-- `v_bits44.bits6`, as (root marker present, digits).  The root marker can
only be the first digit, present iff the first token is `V`; while it is the
last digit a further `V` increments it, as any positive last digit. -/
def bits6 (toks : List Tok) : Option (Bool × List ℕ) := do
  let ds ← toks.foldlM (fun out t =>
    match t with
    | .W => some (out ++ [0])
    | .D => some (out ++ [1])
    | .V =>
      match out.getLast? with
      | none => some [2]
      | some x => if 1 ≤ x then some (out.dropLast ++ [x + 1]) else some (out ++ [2])
    | _ => none) []
  pure (toks.head? = some Tok.V, ds)

/-- `v_bits44.v7`: the marked root seed φ(r, 0) plus the v4 value of the tail
(a lone leading root unit is dropped). -/
def v7 (toks : List Tok) : Option VNote := do
  let (isRoot, digits) ← bits6 toks
  if !isRoot then v4 (digits.length + 1) digits
  else
    match digits with
    | [] => none
    | [r] => some (P (nat r) zero)
    | r :: _ =>
      let seed := P (nat r) zero
      let ds := if (units digits).head? = some [r] then digits.tail else digits
      (add seed ·) <$> v4 (ds.length + 1) ds

/-- `v_bits44.B7`: B(r) = φ(1, φ(1, ω^r)). -/
def B7 (toks : List Tok) : Option VNote :=
  (fun r => P ONE (P ONE (w r))) <$> v7 toks

/-- `token_value.parse_p2_v7_copies`: the W/D/V parse with
W = (0,1,2,1), D = (0,2), V = (0,2,1).  Python enumerates all parses and
requires exactly one; the parse is deterministic (W is separated from D/V by
its second entry, and after a V match the D branch would continue at a `1`,
where no piece starts), so this greedy V-before-D parse is the same. -/
def p2Copies : ℕ → List ℕ → Option (List Tok)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, l@(_ :: _) =>
    if l.take 4 = [0, 1, 2, 1] then (Tok.W :: ·) <$> p2Copies fuel (l.drop 4)
    else if l.take 3 = [0, 2, 1] then (Tok.V :: ·) <$> p2Copies fuel (l.drop 3)
    else if l.take 2 = [0, 2] then (Tok.D :: ·) <$> p2Copies fuel (l.drop 2)
    else none

/-! ## `token_tree` with `P2_V7_EXPERIMENT` on -/

/-- `token_tree.copy_rank` with P2: words containing V by `v7`, W/D words by
the binary rank. -/
def copyRankP2 (copies : List Tok) : Option VNote :=
  if Tok.V ∈ copies then v7 copies
  else some (binV (copies.map fun t => if t = .W then 0 else 1))

open FT in
/-- The token loop of `token_tree.fold` with P2 (v7 copy rank, the fresh
iterated `E` offset rule ε_(s + amount)). -/
def foldLoopP2 (general : Bool) (base offset : FT) :
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
          if general then (some <$> copyRankP2 copies) else some none
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
              if general ∧ fresh ∧ iterated then
                -- P2: ε_(s + amount), s the index of the next ε above the offset
                match nextFp VNote.ONE (ord offset) with
                | .cons a s .zero =>
                  if a = VNote.ONE then
                    some (plus base (epsilon (plus (ofOrd s) amount) none))
                  else none
                | _ => none
              else if fresh ∧ general ∧ ¬iterated ∧ ¬ VNote.lt (ord offset) VNote.E0 then
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
            foldLoopP2 general base offset fuel r3 v false ad'

open FT in
/-- `token_tree.fold` with P2 (TAIL_S / RELTAIL / movable-one / cut-copy off). -/
def foldP2 (tokens : List Tok) (boundary general : Bool) : Option FT := do
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
      let rank ← copyRankP2 pre
      let off ← copyRankP2 rootCopy
      pure (if j ≠ 0 then epsilon (power (ofOrd rank) none) none else epsilon nil none, ofOrd off)
    else if boundary then pure (epsilon (power omega none) none, omega)
    else pure (epsilon (if j = 0 then nil else power (natural j) none) none, natural (j + 1))
  foldLoopP2 general bo.1 bo.2 (tokens.length + 1) (tokens.drop j) bo.1 true 0

/-- `token_tree.block_value` with P2.  Root-V blocks `(2,1,0,2,1,…)` go to the
general fold directly; otherwise `known_block_tree` (whose non-general folds
do not depend on the P2 flag beyond the `Z`/`L` parse, already in
`ValueDef.ttParse`), then the general fold. -/
def ttBlockP2 (u : List ℕ) : Option VNote :=
  let general : Option VNote := do
    let toks ← ttParse true (u.length + 1) (u.drop 2)
    let f ← foldP2 toks false true
    pure (P ONE f.ord)
  if u.take 5 = [2, 1, 0, 2, 1] then general
  else
    match knownBlock u with
    | some v => some v
    | none => if u.take 2 = [2, 1] then general else none

def ttValueP2Aux : ℕ → List ℕ → Option VNote
  | 0, _ => none
  | fuel + 1, s =>
    if s.take 2 ≠ [0, 0] ∨ s.any (· > 2) then none
    else if s.length > 2 ∧ s.getLast? = some 0 then succ <$> ttValueP2Aux fuel s.dropLast
    else (add (nat 2) ·) <$> bodyGen ttBlockP2 ((s.drop 2).length + 1) (s.drop 2)

/-- `token_tree.value` with P2. -/
def ttValueP2 (s : List ℕ) : Option VNote := ttValueP2Aux (s.length + 1) s

/-! ## `token_value` with P2 -/

/-- `token_value.block_value` (P1_ROOT, P1_V_BITS and P2_V7 on).  The P1-root
branch `u[:7] = (2,1,0,2,0,2,1)` runs `token_tree` with its P2 flag off, as in
Python (`ValueDef.ttBlock`). -/
def tvBlockP2Aux : ℕ → List ℕ → Option VNote
  | 0, _ => none
  | fuel + 1, u =>
    let v7root : Option VNote :=
      if u.take 5 = [2, 1, 0, 2, 1] then
        match (p2Copies (u.length + 1) (u.drop 2)).bind B7 with
        | some v => some v
        | none => ttBlockP2 u
      else none
    match v7root with
    | some v => some v
    | none =>
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
            let x ← tvBlockP2Aux fuel [2, 1, 0, 2]
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
                match tvBlockP2Aux fuel base with
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

def tvBlockP2 (u : List ℕ) : Option VNote := tvBlockP2Aux (u.length + 1) u

/-- `token_value.value` together with `p1_root_candidate`, with P2. -/
def valP2Aux : ℕ → List ℕ → Option VNote
  | 0, _ => none
  | fuel + 1, s =>
    if s.take 2 ≠ [0, 0] ∨ s.any (· > 2) then none
    else if s.length > 2 ∧ s.getLast? = some 0 then succ <$> valP2Aux fuel s.dropLast
    else
      match bodyGen tvBlockP2 ((s.drop 2).length + 1) (s.drop 2) with
      | some v => some (add (nat 2) v)
      | none =>
        -- p1_root_candidate (P2 on: the whole of [root, P2))
        let root := [0, 0, 2, 1, 0, 2]
        let p2 := root ++ [1, 1]
        if s.take 6 ≠ root then none
        else if !lexLt s p2 then none
        else if s = root ++ [0, 2, 1] then B7 [Tok.V]
        else if s = root ++ [0, 2, 0, 1] then
          (fun x => w (succ x)) <$> valP2Aux fuel (root ++ [0, 2])
        else if s = root ++ [0, 2, 1, 0, 1] then
          (fun x => w (succ x)) <$> valP2Aux fuel (root ++ [0, 2, 1])
        else ttValueP2 s

/-- The evaluator with P2: `some v` is the Python `value(s)`, `none` is `Unknown`. -/
def valP2 (S : List ℕ) : Option VNote := valP2Aux (S.length + 1) S

end ValueDefP2

/-- The conjectural ordinal translation of an SSOS sequence with the P2
extension (0 where the evaluator is undecided). -/
noncomputable def oValP2 (S : List ℕ) : Ordinal.{0} :=
  match ValueDefP2.valP2 S with
  | some v => VNote.toOrd v
  | none => 0

end SSOS
