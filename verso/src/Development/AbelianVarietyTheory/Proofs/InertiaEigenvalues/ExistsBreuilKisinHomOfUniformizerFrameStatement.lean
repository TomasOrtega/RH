import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinHomOfUniformizerFrame
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.exists_hom_of_frame` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsBreuilKisinHomOfUniformizerFrame.lean&line=127#L127)
-/
theorem _root_.GlobalTheory.T.exists_breuilKisinHom_of_uniformizerFrame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (d v : C.A), IsFrame bk C d v → C.D.δ v = 0 → ∃ g : Hom bk.prism C, BK.hf g X = v := by
  first | exact @GlobalTheory.BSP.exists_hom_of_frame | exact GlobalTheory.BSP.exists_hom_of_frame | (intros; apply GlobalTheory.BSP.exists_hom_of_frame <;> assumption)
