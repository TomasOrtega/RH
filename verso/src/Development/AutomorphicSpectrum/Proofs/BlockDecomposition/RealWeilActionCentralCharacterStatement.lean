import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionCentralCharacter
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CenTheta.RealCentral.piRc_central` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRealWeilActionCentralCharacter.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.real_weil_action_central_character : ∀ (n : ℤ) (t : ℝ) (a : ℝˣ) (g : GL (Fin 2) ℝ) (x : ℂ), piRc (chC n (Complex.I * t)) (dg2 a a * g) (PhiInf n) x = omR n t a * piRc (chC n (Complex.I * t)) g (PhiInf n) x := by
  first | exact @GlobalTheory.CompanionTheory.CenTheta.RealCentral.piRc_central | exact GlobalTheory.CompanionTheory.CenTheta.RealCentral.piRc_central | (intros; apply GlobalTheory.CompanionTheory.CenTheta.RealCentral.piRc_central <;> assumption)
