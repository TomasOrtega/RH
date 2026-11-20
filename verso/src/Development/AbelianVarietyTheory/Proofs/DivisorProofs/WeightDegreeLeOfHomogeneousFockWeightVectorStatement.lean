import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeLeOfHomogeneousFockWeightVector
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeightDegreeLeOfHomogeneousFockWeightVector.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.weightDegree_le_of_homogeneous_fockWeightVector : ∀ (p q r s : ℕ), (∀ (d : ℕ) (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 → P ∈ wtSub (fockAct1 p q r s) μ → degW (cPair r s) μ ≤ d) ∧ (∀ (d : ℕ) (μ : Ix r s → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 → P ∈ wtSub (fockAct2 p q r s) μ → degW (cPair p q) μ ≤ d) := by
  first | exact @GlobalTheory.FockAlg.degW_le_of_homog_wtSub | exact GlobalTheory.FockAlg.degW_le_of_homog_wtSub | (intros; apply GlobalTheory.FockAlg.degW_le_of_homog_wtSub <;> assumption)
