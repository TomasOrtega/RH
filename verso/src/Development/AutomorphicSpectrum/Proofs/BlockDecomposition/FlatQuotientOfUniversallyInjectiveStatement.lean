import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatQuotientOfUniversallyInjective
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFlatQuotientOfUniversallyInjective.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.flat_quotient_of_universally_injective : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [Module.Flat R B] (f : A →ₗ[R] B), (∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (f.lTensor M)) → Module.Flat R (B ⧸ LinearMap.range f) := by
  first | exact @GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective | exact GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective | (intros; apply GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective <;> assumption)
