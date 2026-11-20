import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyCompletedLocalizationPrism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.GenAway₂` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNonemptyCompletedLocalizationPrism.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.nonempty_completedLocalizationPrism : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A), GenAway B f d → Nonempty (LocP B f d) := by
  first | exact @GlobalTheory.BSP.GenAway₂ | exact GlobalTheory.BSP.GenAway₂ | (intros; apply GlobalTheory.BSP.GenAway₂ <;> assumption)
