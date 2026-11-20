import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsVariablePowSmulEqZeroOfFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMemA
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UPow.exists_uIn_pow_smul_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsVariablePowSmulEqZeroOfFiniteLength.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.exists_variable_pow_smul_eq_zero_of_finiteLength : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (M : Type) [AddCommGroup M] [Module (A O K) M], IsFiniteLength (A O K) M → ∃ n : ℕ, ∀ x : M, (uIn (A O K)) ^ n • x = 0 := by
  first | exact @GlobalTheory.UPow.exists_uIn_pow_smul_eq_zero | exact GlobalTheory.UPow.exists_uIn_pow_smul_eq_zero | (intros; apply GlobalTheory.UPow.exists_uIn_pow_smul_eq_zero <;> assumption)
