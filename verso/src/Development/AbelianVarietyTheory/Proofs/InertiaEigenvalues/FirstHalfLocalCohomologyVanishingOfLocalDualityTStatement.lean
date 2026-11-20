import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ScalarFrob.firstHalf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFirstHalfLocalCohomologyVanishingOfLocalDualityT.lean&line=296#L296)
-/
theorem _root_.GlobalTheory.T.firstHalfLocalCohomologyVanishing_of_localDualityTheorems : LocalFiniteness → LocalTateDuality → LocalEulerChar → TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstHalf i s := by
  first | exact @GlobalTheory.ScalarFrob.firstHalf | exact GlobalTheory.ScalarFrob.firstHalf | (intros; apply GlobalTheory.ScalarFrob.firstHalf <;> assumption)
