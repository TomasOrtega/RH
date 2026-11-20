import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryFlowCoeffEqOfTaylorSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FUnitaryFlowCoeffEqOfTaylorSeries.lean&line=190#L190)
-/
theorem _root_.GlobalTheory.T.unitaryFlow_coeff_eq_of_taylor_series : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (U : ℝ → (H →L[ℂ] H)) (x : ℕ → H) (y : H) (φ φ₀ : ℝ → ℂ), U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ t v, ‖U t v‖ = ‖v‖) → (∀ m, HasDerivAt (fun t => U t (x m)) (x (m + 1)) 0) → AnalyticOnNhd ℝ φ Set.univ → AnalyticAt ℝ φ₀ 0 → (∀ m, iteratedDeriv m φ 0 = ⟪y, x m⟫_ℂ) → (∀ m, iteratedDeriv m φ₀ 0 = ⟪x 0, x m⟫_ℂ) → ∀ t, φ t = ⟪y, U t (x 0)⟫_ℂ := by
  first | exact @GlobalTheory.SphJet.unitaryFlow_coeff_eq_of_taylor | exact GlobalTheory.SphJet.unitaryFlow_coeff_eq_of_taylor | (intros; apply GlobalTheory.SphJet.unitaryFlow_coeff_eq_of_taylor <;> assumption)
