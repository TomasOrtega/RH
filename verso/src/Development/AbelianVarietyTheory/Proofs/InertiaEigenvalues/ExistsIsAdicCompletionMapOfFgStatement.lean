import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsAdicCompletionMapOfFg
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.isCompl_exists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsIsAdicCompletionMapOfFg.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.exists_isAdicCompletionMap_of_fg : ∀ (L : Type) [CommRing L] (J : Ideal L), J.FG → ∃ (Q : Type) (_ : CommRing Q) (i : L →+* Q), IsCompl i J := by
  first | exact @GlobalTheory.BSP.isCompl_exists | exact GlobalTheory.BSP.isCompl_exists | (intros; apply GlobalTheory.BSP.isCompl_exists <;> assumption)
