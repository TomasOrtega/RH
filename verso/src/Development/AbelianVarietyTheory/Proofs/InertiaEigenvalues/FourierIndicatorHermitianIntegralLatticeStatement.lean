import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierIndicatorHermitianIntegralLattice
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.fourB_indicator_intLattice` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFourierIndicatorHermitianIntegralLattice.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.fourier_indicator_hermitianIntegralLattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) (B : A.L → A.L → ℂ), (∀ y' y, B y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) → IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → ∀ μ : Measure A.L, μ.IsAddHaarMeasure → ∀ y, fourB μ B (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1) y = ((μ {y : A.L | ∀ i, ‖j y i‖ ≤ 1}).toReal : ℂ) * Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1 y := by
  first | exact @GlobalTheory.JR.fourB_indicator_intLattice | exact GlobalTheory.JR.fourB_indicator_intLattice | (intros; apply GlobalTheory.JR.fourB_indicator_intLattice <;> assumption)
