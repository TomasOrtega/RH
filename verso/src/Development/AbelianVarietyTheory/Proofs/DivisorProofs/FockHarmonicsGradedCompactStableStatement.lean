import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FockAlg.harm_graded_stable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFockHarmonicsGradedCompactStable.lean&line=211#L211)
-/
theorem _root_.GlobalTheory.T.fockHarmonics_graded_compactStable : ∀ (p q r s : ℕ) (S : Set (Pol p q r s)), (S = harm1 p q r s ∨ S = harm2 p q r s ∨ S = jointHarm p q r s) → (Submodule.span ℂ S : Set (Pol p q r s)) = S ∧ KStable (fockAct1 p q r s) (Submodule.span ℂ S) ∧ KStable (fockAct2 p q r s) (Submodule.span ℂ S) ∧ ∀ P ∈ S, ∀ d : ℕ, homogeneousComponent d P ∈ S := by
  first | exact @GlobalTheory.FockAlg.harm_graded_stable | exact GlobalTheory.FockAlg.harm_graded_stable | (intros; apply GlobalTheory.FockAlg.harm_graded_stable <;> assumption)
