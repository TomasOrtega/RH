import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElementsSelmerFormsSmallCorank
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsElementsSelmerFormsSmallCorank.lean&line=557#L557)
-/
theorem _root_.GlobalTheory.T.exists_elements_selmerForms_small_corank : GlobalFiniteness → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw), (∀ s, GalHyp bkP i s → SpanOdd i s ∧ SpanTwo i s ∧ EqDim bkP i s) → ChooseH bkP i := by
  first | exact @GlobalTheory.ChooseForms.chooseH | exact GlobalTheory.ChooseForms.chooseH | (intros; apply GlobalTheory.ChooseForms.chooseH <;> assumption)
