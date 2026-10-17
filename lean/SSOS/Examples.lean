import SSOS.SequenceOrdinal

/-! Regression examples from the rev 76153 handover, proved by kernel reduction. -/

namespace SSOS

example : Seq.step [0,0,1] 1 = .inr ([0,0,0,0], 2) := by decide +kernel
example : Seq.step [0,0,1,0,1] 1 = .inr ([0,0,1,0,0,1,0,0], 2) := by decide +kernel
example : Seq.step [0,0,1,1] 1 = .inr ([0,0,1,0,1,0], 2) := by decide +kernel
example : Seq.step [0,0,1,1,0,1] 1 = .inr ([0,0,1,1,0,0,1,1,0,0], 2) := by decide +kernel
example : Seq.step [0,0,1,0,0,1,1] 1 = .inr ([0,0,1,0,0,1,0,1,0], 2) := by decide +kernel
example : Seq.step [0,0,1,1,1] 2 = .inr ([0,0,1,1,0,1,1,0,1,1,0], 3) := by decide +kernel
example : Seq.step [0,0,2] 1 = .inr ([0,0,1,1], 2) := by decide +kernel
example : Seq.step [0,0,2,1] 1 = .inr ([0,0,2,0,2,0], 2) := by decide +kernel

example : Seq.step [] 3 = .inl 3 := by decide +kernel
example : Seq.step [0,0,1,0] 3 = .inr ([0,0,1], 4) := by decide +kernel

-- The nonstandard counterexample must remain a counterexample.
example : Seq.fs [0,0,1,0,1,1,0,1] 2 = [0,0,1,0,1,1,0,0,1,1,0,0] := by decide +kernel

example : encode [U.b [U.z, U.b [], U.z]] = [0,0,1,0,1,1,0,1] := by
  simp [encode, raiseBits, raiseBit]
example : encode (E [U.b [U.z, U.b [], U.z]] 2) =
    [0,0,1,0,1,1,0,0,1,0,1,1,0,0] := by
  simp [encode, E, H, raiseBits, raiseBit]

-- One cut computation proves the bridge for EVERY k >= 1 for each source.
example : CutCorrect [] [] := by
  simp [CutCorrect, encode, parts, raiseBits]; decide +kernel

example : CutCorrect [U.b []] [] := by
  simp [CutCorrect, encode, parts, raiseBits, liftBits]; decide +kernel

example : CutCorrect [U.z] [] := by
  simp [CutCorrect, encode, parts, raiseBits, raiseBit]; decide +kernel

example : CutCorrect [U.z, U.b []] [] := by
  simp [CutCorrect, encode, parts, raiseBits, raiseBit]; decide +kernel

example : CutCorrect [U.b []] [U.z, U.z, U.b []] := by
  simp [CutCorrect, encode, parts, raiseBits, raiseBit, liftBits];
    decide +kernel

example : CutCorrect [U.b [U.b []]] [] := by
  simp [CutCorrect, encode, parts, raiseBits, liftBits]; decide +kernel

example : ¬CutCorrect [U.z, U.b [], U.z] [] := by
  simp [CutCorrect, encode, parts, raiseBits, raiseBit]; decide +kernel

-- Standardness of the SEQUENCE does not suffice for an arbitrary encoding tree.
example : encode [U.b [], U.b []] = encode [U.b [U.b []]] := by
  simp [encode, raiseBits, raiseBit]

example : Standard (encode [U.b [], U.b []]) := by
  simpa [encode, raiseBits, raiseBit] using Standard.tower 2

example : ¬CutCorrect [] [U.b []] := by
  simp [CutCorrect, encode, parts, raiseBits]; decide +kernel

example : ¬Canonical [U.b [], U.b []] := by
  intro h
  cases h with
  | block _ _ hg => exact hg

-- The parser reconstructs maximal blocks, including single-zero merges.
example : parse [1,0,1,1,0,1] = [U.b [U.z, U.b [], U.z]] := by
  simp [parse, parseStep, snocOne]

example : parse [1,0,0,1] = [U.b [], U.z, U.z, U.b []] := by
  simp [parse, parseStep, snocOne]

example : o [] = 0 := by simp [o]
example : o [0] = 1 := by simp [o]

end SSOS
