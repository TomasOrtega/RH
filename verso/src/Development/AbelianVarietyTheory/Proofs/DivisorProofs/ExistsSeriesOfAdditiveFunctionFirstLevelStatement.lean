import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeriesOfAdditiveFunctionFirstLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Katz.Chart.exists_series_of_cobOne_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSeriesOfAdditiveFunctionFirstLevel.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.exists_series_of_additive_function_first_level : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ b : G.A 1, cobOne k (G.A 1) b = 0 → ∃ (κ : MvPowerSeries (Fin d ⊕ Fin d) k) (B : MvPowerSeries (Fin d) k), IsCoc μ κ ∧ constantCoeff κ = 0 ∧ cob1 μ B = pull2 (nmul μ p) κ ∧ c.ev 1 B = b := by
  first | exact @GlobalTheory.Katz.Chart.exists_series_of_cobOne_eq_zero | exact GlobalTheory.Katz.Chart.exists_series_of_cobOne_eq_zero | (intros; apply GlobalTheory.Katz.Chart.exists_series_of_cobOne_eq_zero <;> assumption)
