import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormRealCentralCharacterEqOne
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
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNormRealCentralCharacterEqOne.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.norm_real_central_character_eq_one : ∀ (n : ℤ) (t : ℝ) (a : ℝˣ), ‖omR n t a‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CenTheta.norm_omR | exact GlobalTheory.CompanionTheory.CenTheta.norm_omR | (intros; apply GlobalTheory.CompanionTheory.CenTheta.norm_omR <;> assumption)
