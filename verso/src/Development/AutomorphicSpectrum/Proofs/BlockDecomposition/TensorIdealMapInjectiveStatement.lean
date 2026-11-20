import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorIdealMapInjective
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTensorIdealMapInjective.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.tensor_ideal_map_injective : ∀ (O O' R : Type) [CommRing O] [CommRing O'] [Nontrivial O'] [Algebra O O'] [Module.Free O O'] [CommRing R] [Algebra O R] (I : Ideal R) (x : R), (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) x ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) I → x ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.Descent.mem_of_includeRight_mem_map | exact GlobalTheory.CompanionTheory.Descent.mem_of_includeRight_mem_map | (intros; apply GlobalTheory.CompanionTheory.Descent.mem_of_includeRight_mem_map <;> assumption)
