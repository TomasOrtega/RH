import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFinite
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinTranslate.isAutFunSm_rTr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIsSmoothAutomorphicRightTranslateFinite.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.isSmoothAutomorphic_rightTranslate_finite : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (κ : GA D V), κ ∈ GfC V → ∀ φ : GA D V → ℂ, IsAutFunSm θ V φ → IsAutFunSm θ V (rTr V κ φ) := by
  first | exact @GlobalTheory.FinTranslate.isAutFunSm_rTr | exact GlobalTheory.FinTranslate.isAutFunSm_rTr | (intros; apply GlobalTheory.FinTranslate.isAutFunSm_rTr <;> assumption)
