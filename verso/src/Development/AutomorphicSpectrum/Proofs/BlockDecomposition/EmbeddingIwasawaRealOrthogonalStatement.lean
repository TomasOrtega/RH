import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbeddingIwasawaRealOrthogonal
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEmbeddingIwasawaRealOrthogonal.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.embedding_iwasawa_real_orthogonal : ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 → GL2LocalData.emR (dg2 (a * b) b * k) = dg (a * b) b 1 * GL2LocalData.emR k ∧ GL2LocalData.emR k ∈ O3 := by
  first | exact @GlobalTheory.CompanionTheory.GL2Factorization.EmC.emR_iwasawa | exact GlobalTheory.CompanionTheory.GL2Factorization.EmC.emR_iwasawa | (intros; apply GlobalTheory.CompanionTheory.GL2Factorization.EmC.emR_iwasawa <;> assumption)
