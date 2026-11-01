import Mathlib.SetTheory.Ordinal.Veblen

/-!
# A computable Veblen notation mirroring `ordinal.py`

`VNote.cons a b r` is the term `φ(a, b)` followed by the rest `r`; `zero` is
the empty sum.  This is the Python tuple `(('p', a, b),) + r`.  Normal forms
list the principal terms in non-increasing order, and `P` collapses
`φ(a, φ(c, d))` with `c > a` to `φ(c, d)`, exactly like `ordinal.P`.

All operations are the Python ones transcribed literally (including their
behaviour on non-normal input), so that `showV` reproduces `ordinal.show`.
`toOrd` reads a notation as an ordinal using Mathlib's `Ordinal.veblen`,
whose convention is `veblen 0 b = ω ^ b` (= `φ(0, b)`).
-/

namespace SSOS

inductive VNote where
  | zero : VNote
  | cons (a b rest : VNote) : VNote
  deriving DecidableEq, Repr, Inhabited

namespace VNote

theorem one_le_sizeOf (x : VNote) : 1 ≤ sizeOf x := by
  cases x <;> simp; omega

/-- `ordinal.cmp`, with `ordinal.cmp_p` inlined on the head terms. -/
def cmp : VNote → VNote → Ordering
  | zero, zero => .eq
  | zero, cons .. => .lt
  | cons .., zero => .gt
  | cons a b r, cons c d r' =>
    let cp : Ordering :=
      match cmp a c with
      | .eq => cmp b d
      | .lt => if cmp b (cons c d zero) = .lt then .lt else .gt
      | .gt => if cmp d (cons a b zero) = .lt then .gt else .lt
    if cp = .eq then cmp r r' else cp
termination_by x y => sizeOf x + sizeOf y
decreasing_by
  all_goals simp_wf
  all_goals (have := one_le_sizeOf r; have := one_le_sizeOf r'; omega)

def lt (x y : VNote) : Bool := cmp x y = .lt

/-- The terms as a list of `(a, b)` pairs. -/
def toList : VNote → List (VNote × VNote)
  | zero => []
  | cons a b r => (a, b) :: toList r

/-- Prepend a list of terms to a notation. -/
def ofListApp : List (VNote × VNote) → VNote → VNote
  | [], y => y
  | (a, b) :: l, y => cons a b (ofListApp l y)

def ofList (l : List (VNote × VNote)) : VNote := ofListApp l zero

def single (a b : VNote) : VNote := cons a b zero

def ONE : VNote := single zero zero

/-- `ordinal.P`: φ(a, b), normalized. -/
def P (a b : VNote) : VNote :=
  match b with
  | cons c _ zero => if cmp c a = .gt then b else cons a b zero
  | _ => cons a b zero

def w (b : VNote) : VNote := P zero b

def OMEGA : VNote := single zero ONE

def E0 : VNote := P ONE zero

def nat (n : ℕ) : VNote := ofList (List.replicate n (zero, zero))

/-- `ordinal.add`. -/
def add (x y : VNote) : VNote :=
  match y with
  | zero => x
  | cons c d _ =>
    let keep := (x.toList.reverse.dropWhile
      (fun t => cmp (single t.1 t.2) (single c d) = .lt)).reverse
    ofListApp keep y

def succ (x : VNote) : VNote := add x ONE

/-- `evalord.next_fp`: the least φ(c, d) greater than `x`. -/
def nextFp (c : VNote) : VNote → VNote
  | zero => P c zero
  | cons e f r =>
      if lt (cons e f r) (P c zero) then P c zero
      else match cmp e c with
        | .eq => P c (succ f)
        | .gt => P c (succ (single e f))
        | .lt => nextFp c f

/-! ## Printing, exactly as `ordinal.show` -/

/-- `ordinal._top`: does a character of `chars` occur outside brackets? -/
def topHas (s : String) (chars : List Char) : Bool :=
  let rec go : List Char → Int → Bool
    | [], _ => false
    | ch :: cs, d =>
      if ch = '(' ∨ ch = '{' then go cs (d + 1)
      else if ch = ')' ∨ ch = '}' then go cs (d - 1)
      else if d = 0 ∧ ch ∈ chars then true
      else go cs d
  go s.toList 0

def isDigits (s : String) : Bool := !s.isEmpty && s.toList.all Char.isDigit

/-- `ordinal._wrap`. -/
def wrap (s : String) : String :=
  let wNum := match s.toList with
    | 'w' :: rest => !rest.isEmpty && rest.all Char.isDigit
    | _ => false
  if topHas s ['+', '·'] || wNum then "(" ++ s ++ ")" else s

/-- `ordinal.show` on a list of rendered terms (grouping equal neighbours). -/
def render (l : List (String × (VNote × VNote))) : String :=
  match l with
  | [] => "0"
  | _ =>
    let rec go : List (String × (VNote × VNote)) → ℕ → List String
      | [], _ => []
      | (s, t) :: rest, fuel =>
        match fuel with
        | 0 => []
        | fuel + 1 =>
          let same := rest.takeWhile (fun u => u.2 = t)
          let c := same.length + 1
          let s' := if s = "1" then toString c
            else if c > 1 then (if s = "w" then s ++ toString c else s ++ "·" ++ toString c)
            else s
          s' :: go (rest.drop same.length) fuel
    "+".intercalate (go l l.length)

/-- `ordinal.show_p`, given the rendered `show a` and `show b`. -/
def showP (a b : VNote) (sa sb : String) : String :=
  match a with
  | zero =>
    match b with
    | zero => "1"
    | _ => if b = ONE then "w" else "w^" ++ wrap sb
  | _ =>
    let l := a.toList
    let name : Option String :=
      if l.all (fun t => t = (zero, zero)) then
        match l.length with
        | 1 => some "e" | 2 => some "z" | 3 => some "h" | _ => none
      else none
    match name with
    | some nm => nm ++ (if isDigits sb then sb else "_" ++ wrap sb)
    | none => "phi(" ++ sa ++ "," ++ sb ++ ")"

/-- Each term with its rendering `show_p`. -/
def rendered : VNote → List (String × (VNote × VNote))
  | zero => []
  | cons a b r => (showP a b (render (rendered a)) (render (rendered b)), (a, b)) :: rendered r

/-- `ordinal.show` (named `showV` since `show` is a keyword). -/
def showV (x : VNote) : String := render (rendered x)

/-- The ordinal denoted: `φ(a, b) + r` with `φ = Ordinal.veblen`. -/
noncomputable def toOrd : VNote → Ordinal.{0}
  | zero => 0
  | cons a b r => Ordinal.veblen (toOrd a) (toOrd b) + toOrd r

end VNote
end SSOS
