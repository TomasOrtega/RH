import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowKillsFiniteLengthIntegralPowerSeri
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiagScaleApply
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PowKill.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsPrimePowKillsFiniteLengthIntegralPowerSeri.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.exists_prime_pow_kills_finiteLength_integralPowerSeries : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (Mo : Type) [AddCommGroup Mo] [Module (A O K) Mo], IsFiniteLength (A O K) Mo → ∃ m : ℕ, ∀ q : Mo, ((l : A O K) ^ m) • q = 0 := by
  first | exact @GlobalTheory.PowKill.main | exact GlobalTheory.PowKill.main | (intros; apply GlobalTheory.PowKill.main <;> assumption)
