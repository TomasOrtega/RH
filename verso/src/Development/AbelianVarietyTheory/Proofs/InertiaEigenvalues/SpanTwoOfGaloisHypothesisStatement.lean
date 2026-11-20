import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTwoOfGaloisHypothesis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSpanTwoOfGaloisHypothesis.lean&line=196#L196)
-/
theorem _root_.GlobalTheory.T.span_two_of_galois_hypothesis : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → SpanTwo i s := by
  first | exact @GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp | exact GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp | (intros; apply GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp <;> assumption)
