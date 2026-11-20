import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointShapeUniqueAndDegWEq
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JointShapeUniq.jointShape_unique_deg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FJointShapeUniqueAndDegWEq.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.jointShape_unique_and_degW_eq : ∀ (p q r s : ℕ) (μ μ₁ : Ix p q → ℚ) (μ' μ₁' : Ix r s → ℚ), JointShape p q r s μ μ' → JointShape p q r s μ₁ μ₁' → (μ = μ₁ ↔ μ' = μ₁') ∧ degW (cPair r s) μ = degW (cPair p q) μ' := by
  first | exact @GlobalTheory.JointShapeUniq.jointShape_unique_deg | exact GlobalTheory.JointShapeUniq.jointShape_unique_deg | (intros; apply GlobalTheory.JointShapeUniq.jointShape_unique_deg <;> assumption)
