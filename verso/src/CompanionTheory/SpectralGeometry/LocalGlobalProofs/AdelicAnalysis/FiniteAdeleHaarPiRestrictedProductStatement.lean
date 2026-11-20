import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarPiRestrictedProduct
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.AfBox.pi_box` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FFiniteAdeleHaarPiRestrictedProduct.lean&line=136#L136)
-/
theorem _root_.GlobalTheory.T.finite_adele_haar_pi_restricted_product : ∀ (F : Type) [Field F] [NumberField F] (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (ι : Type) [Fintype ι] (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (ι → Fv F v)), (∀ v, MeasurableSet (A v)) → (Measure.pi fun _ : ι => lf) {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A v) ∧ ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} = ∏ v ∈ S, (Measure.pi fun _ : ι => lam v) (A v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.AfBox.pi_box | exact GlobalTheory.CompanionTheory.SW.AfBox.pi_box | (intros; apply GlobalTheory.CompanionTheory.SW.AfBox.pi_box <;> assumption)
