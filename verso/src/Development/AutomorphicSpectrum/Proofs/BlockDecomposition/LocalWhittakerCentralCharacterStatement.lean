import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWhittakerCentralCharacter
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
Apply `GlobalTheory.CompanionTheory.CenTheta.W_central` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalWhittakerCentralCharacter.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.local_whittaker_central_character : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → ∀ (a : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)), m.W (dg2 a a * g) = omW m a * m.W g := by
  first | exact @GlobalTheory.CompanionTheory.CenTheta.W_central | exact GlobalTheory.CompanionTheory.CenTheta.W_central | (intros; apply GlobalTheory.CompanionTheory.CenTheta.W_central <;> assumption)
