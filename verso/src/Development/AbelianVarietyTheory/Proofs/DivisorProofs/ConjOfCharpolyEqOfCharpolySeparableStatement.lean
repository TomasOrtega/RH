import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjOfCharpolyEqOfCharpolySeparable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclicVectorOfSeparableCharpoly
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConjOfCharpolyEqOfCharpolySeparable.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.conj_of_charpoly_eq_of_charpoly_separable : ∀ (R : Type) [Field R] (m : ℕ) (N U : Matrix (Fin m) (Fin m) R), N.charpoly = U.charpoly → N.charpoly.Separable → ∃ P : GL (Fin m) R, N * P.val = P.val * U := by
  first | exact @GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable | exact GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable | (intros; apply GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable <;> assumption)
