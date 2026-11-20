import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImaginaryQuadraticAdelicNormBound
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open scoped NumberField.AdeleRing Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.MajHeightK.adelicNorm_ratVec_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FImaginaryQuadraticAdelicNormBound.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.imaginary_quadratic_adelic_norm_bound : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (w : InfinitePlace K) (M : ℕ), 0 < M → ∀ z : Fin 3 → K, (∀ i, ∃ a : 𝓞 K, (a : K) = (M : K) * z i) → Reduction.adelicNorm (Reduction.ratVec z : Fin 3 → 𝔸[K]) ≤ (M : ℝ) ^ 2 * (∑ i, w (z i)) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.MajHeightK.adelicNorm_ratVec_le | exact GlobalTheory.CompanionTheory.MajHeightK.adelicNorm_ratVec_le | (intros; apply GlobalTheory.CompanionTheory.MajHeightK.adelicNorm_ratVec_le <;> assumption)
