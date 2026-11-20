import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat
import ReciprocityTheory.GaloisValuations.Global
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertiaLift.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteGaloisInertiaLiftsAbsoluteInertiaRat.lean&line=169#L169)
-/
theorem _root_.GlobalTheory.T.finiteGaloisInertia_lifts_absoluteInertia_rat : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (M : IntermediateField ℚ Ω) [FiniteDimensional ℚ M] [IsGalois ℚ M] (τ : M ≃ₐ[ℚ] M), (∀ x : M, A.valuation (x : Ω) ≤ 1 → A.valuation ((τ x : Ω) - (x : Ω)) < 1) → (∀ x : M, A.valuation ((τ x : M) : Ω) ≤ 1 ↔ A.valuation (x : Ω) ≤ 1) → ∃ σ ∈ Ine (F := ℚ) A, ∀ x : M, σ (x : Ω) = (τ x : Ω) := by
  first | exact @GlobalTheory.InertiaLift.main | exact GlobalTheory.InertiaLift.main | (intros; apply GlobalTheory.InertiaLift.main <;> assumption)
