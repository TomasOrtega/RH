import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumMatrixCoefficientSq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.vacuum_coef_sq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVacuumMatrixCoefficientSq.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.vacuum_matrix_coefficient_sq : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 → GlobalTheory.IsSiegel (-(Q * P⁻¹)) → ∀ c : ℂ, c ^ 2 * P.det = 1 → (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (GlobalTheory.Published.Metaplectic.holPart s).det = (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 := by
  first | exact @GlobalTheory.vacuum_coef_sq | exact GlobalTheory.vacuum_coef_sq | (intros; apply GlobalTheory.vacuum_coef_sq <;> assumption)
