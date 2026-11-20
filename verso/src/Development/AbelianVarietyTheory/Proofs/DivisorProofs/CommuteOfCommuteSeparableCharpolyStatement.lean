import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteOfCommuteSeparableCharpoly
import Mathlib
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCommuteOfCommuteSeparableCharpoly.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.commute_of_commute_of_charpoly_separable' : ∀ (K : Type) [Field K] (n : ℕ) (y a b : Matrix (Fin n) (Fin n) K), y.charpoly.Separable → a * y = y * a → b * y = y * b → a * b = b * a := by
  first | exact @GlobalTheory.commute_of_commute_separable_charpoly | exact GlobalTheory.commute_of_commute_separable_charpoly | (intros; apply GlobalTheory.commute_of_commute_separable_charpoly <;> assumption)
