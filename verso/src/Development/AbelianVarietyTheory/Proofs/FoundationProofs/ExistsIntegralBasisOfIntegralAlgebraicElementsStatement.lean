import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralBasisOfIntegralAlgebraicElements
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsIntegralBasisOfIntegralAlgebraicElements.lean&line=275#L275)
-/
theorem _root_.GlobalTheory.T.exists_integral_basis_of_integral_algebraic_elements : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt p x) → 0 < v (p : Ω) → v (p : Ω) < 1 → ∀ (d : ℕ) (e : Fin d → Ω), (∀ t, IsInt p (e t) ∧ IsAlgZp p (e t)) → ∃ (E F : ℕ) (π : Ω) (κ : Fin F → Ω) (lam : Fin d → Fin F → Fin E → ℤ_[p]), 1 ≤ E ∧ IsAlgZp p π ∧ v π ^ E = v (p : Ω) ∧ (∀ j, IsInt p (κ j) ∧ IsAlgZp p (κ j)) ∧ (∀ μ : Fin F → ℤ_[p], (∃ j, ¬ (p : ℤ_[p]) ∣ μ j) → v (∑ j, κ j * zp Ω (μ j)) = 1) ∧ ∀ t, e t = ∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * zp Ω (lam t j s) := by
  first | exact @GlobalTheory.K5.OkBasis.okbasis | exact GlobalTheory.K5.OkBasis.okbasis | (intros; apply GlobalTheory.K5.OkBasis.okbasis <;> assumption)
