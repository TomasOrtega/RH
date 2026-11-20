import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerPresentationMatrixOfGaloisCohomology
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SelFun.oneMatrix_of_galoisCohomology` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSelmerPresentationMatrixOfGaloisCohomology.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.selmerPresentationMatrix_of_galois_cohomology : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ThmS bkP := by
  first | exact @GlobalTheory.SelFun.oneMatrix_of_galoisCohomology | exact GlobalTheory.SelFun.oneMatrix_of_galoisCohomology | (intros; apply GlobalTheory.SelFun.oneMatrix_of_galoisCohomology <;> assumption)
