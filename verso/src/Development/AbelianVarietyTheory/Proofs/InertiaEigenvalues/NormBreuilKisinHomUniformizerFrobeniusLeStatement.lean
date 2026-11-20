import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNormBreuilKisinHomUniformizerFrobeniusLe.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ‖toDisc l (BK.hf f X) bk.ρ₀ (BK.hf g X)‖ ≤ bk.ρ₀ ∧ ‖toDisc l (BK.hf f X) bk.ρ₀ (B.D.φ (BK.hf f X))‖ ≤ bk.ρ₀ := by
  first | exact @GlobalTheory.BSP.norm_hf_g_X_and_φ_le | exact GlobalTheory.BSP.norm_hf_g_X_and_φ_le | (intros; apply GlobalTheory.BSP.norm_hf_g_X_and_φ_le <;> assumption)
