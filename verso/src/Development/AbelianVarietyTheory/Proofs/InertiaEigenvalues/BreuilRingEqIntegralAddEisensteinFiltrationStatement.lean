import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilRingEqIntegralAddEisensteinFiltration
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBreuilRingEqIntegralAddEisensteinFiltration.lean&line=146#L146)
-/
theorem _root_.GlobalTheory.T.breuilRing_eq_integral_add_eisensteinFiltration : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (j : ℕ), j < l → ∀ f ∈ S O K e, ∃ g ∈ A O K, ∃ φ ∈ Fil O K l e j, f = g + (φ : K⟦X⟧) := by
  first | exact @GlobalTheory.BK.SDec.S_eq_A_add_Fil | exact GlobalTheory.BK.SDec.S_eq_A_add_Fil | (intros; apply GlobalTheory.BK.SDec.S_eq_A_add_Fil <;> assumption)
