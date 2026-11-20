import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionEisensteinPowIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWeierstrassDivisionEisensteinPowIntegral.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.weierstrass_division_eisensteinPow_integral : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) (f : K⟦X⟧), f ∈ A O K → ∃ (c : Fin (e * n) → O) (g : K⟦X⟧), g ∈ A O K ∧ f = ∑ k : Fin (e * n), C (algebraMap O K (c k)) * X ^ (k : ℕ) + E K l e ^ n * g := by
  first | exact @GlobalTheory.weierstrassDiv_E_pow | exact GlobalTheory.weierstrassDiv_E_pow | (intros; apply GlobalTheory.weierstrassDiv_E_pow <;> assumption)
