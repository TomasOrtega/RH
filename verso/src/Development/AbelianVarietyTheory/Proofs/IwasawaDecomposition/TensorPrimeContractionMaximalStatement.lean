import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorPrimeContractionMaximal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BaseChangeLoc.localization_atPrime_tensor` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTensorPrimeContractionMaximal.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.tensor_prime_contraction_maximal : ∀ (A C R : Type) [CommRing A] [CommRing C] [CommRing R] [Algebra A C] [Algebra A R] (Q : Ideal (C ⊗[A] R)) [Q.IsPrime], ∃ (Q' : Ideal (Localization.AtPrime (Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R)) ⊗[A] R)) (_ : Q'.IsPrime), Q'.comap (Algebra.TensorProduct.includeLeft : Localization.AtPrime (Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R)) →ₐ[A] _ ⊗[A] R) = maximalIdeal _ ∧ (IsDomain (Localization.AtPrime Q') → IsIntegrallyClosed (Localization.AtPrime Q') → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) := by
  first | exact @GlobalTheory.BaseChangeLoc.localization_atPrime_tensor | exact GlobalTheory.BaseChangeLoc.localization_atPrime_tensor | (intros; apply GlobalTheory.BaseChangeLoc.localization_atPrime_tensor <;> assumption)
