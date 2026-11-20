import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfIntegralFiniteAdele
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open scoped NumberField.AdeleRing Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIntegralOfIntegralFiniteAdele.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.integral_of_integral_finite_adele : ∀ (K : Type) [Field K] [NumberField K] (x : K), algebraMap K (FiniteAdeleRing (𝓞 K) K) x ∈ integralFiniteAdeles (𝓞 K) K → ∃ a : 𝓞 K, (a : K) = x := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.exists_integer_of_mem_integralFiniteAdeles | exact GlobalTheory.CompanionTheory.Adelic.exists_integer_of_mem_integralFiniteAdeles | (intros; apply GlobalTheory.CompanionTheory.Adelic.exists_integer_of_mem_integralFiniteAdeles <;> assumption)
