import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscNormMulMultiplicative
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBreuilKisinClosedDiscNormMulMultiplicative.lean&line=146#L146)
-/
theorem _root_.GlobalTheory.T.breuilKisin_closedDisc_norm_mul_multiplicative : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ x y : bk.DS ρ, ‖x * y‖ = ‖x‖ * ‖y‖ := by
  first | exact @GlobalTheory.BSP.GaussMul.norm_mul | exact GlobalTheory.BSP.GaussMul.norm_mul | (intros; apply GlobalTheory.BSP.GaussMul.norm_mul <;> assumption)
