import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomExtOfX
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.BK.hom_ext_of_hf_X` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBreuilKisinPrismHomExtOfX.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.breuilKisin_prism_hom_ext_of_X : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (g g' : Hom bk.prism C), BK.hf g X = BK.hf g' X → g = g' := by
  first | exact @GlobalTheory.BSP.BK.hom_ext_of_hf_X | exact GlobalTheory.BSP.BK.hom_ext_of_hf_X | (intros; apply GlobalTheory.BSP.BK.hom_ext_of_hf_X <;> assumption)
