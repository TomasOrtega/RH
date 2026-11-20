import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWitt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsPrimePowMulEqThetaWitt.lean&line=226#L226)
-/
theorem _root_.GlobalTheory.T.exists_prime_pow_mul_eq_theta_witt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (x : Om l), x ∈ K.1 → x ∈ MaximalUnramifiedExtension l → ∃ (n : ℕ) (w : Wq l bk.a), ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) = ((((l : Om l) ^ n * x : Om l)) : ℂ_[l]) := by
  first | exact @GlobalTheory.UnrWitt.exists_pow_mul_eq_theta | exact GlobalTheory.UnrWitt.exists_pow_mul_eq_theta | (intros; apply GlobalTheory.UnrWitt.exists_pow_mul_eq_theta <;> assumption)
