import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousIwasawaRealParametrization
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GL2Factorization.IwasawaCoord.continuous_iwasawa_coord` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FContinuousIwasawaRealParametrization.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.continuous_iwasawa_real_parametrization : Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => dg2 (p.1 * p.2.1) p.2.1 * p.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.GL2Factorization.IwasawaCoord.continuous_iwasawa_coord | exact GlobalTheory.CompanionTheory.GL2Factorization.IwasawaCoord.continuous_iwasawa_coord | (intros; apply GlobalTheory.CompanionTheory.GL2Factorization.IwasawaCoord.continuous_iwasawa_coord <;> assumption)
