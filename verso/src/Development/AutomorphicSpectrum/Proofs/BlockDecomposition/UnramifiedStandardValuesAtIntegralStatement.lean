import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedStandardValuesAtIntegral
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
Apply `GlobalTheory.CompanionTheory.StdValue.std_unit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnramifiedStandardValuesAtIntegral.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.unramified_standard_values_at_integral : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), Unr c v → m.ok → m.std → ∀ k ∈ integralGL (Qv v) 2, m.W k = 1 ∧ m.val k 0 = 1 := by
  first | exact @GlobalTheory.CompanionTheory.StdValue.std_unit | exact GlobalTheory.CompanionTheory.StdValue.std_unit | (intros; apply GlobalTheory.CompanionTheory.StdValue.std_unit <;> assumption)
