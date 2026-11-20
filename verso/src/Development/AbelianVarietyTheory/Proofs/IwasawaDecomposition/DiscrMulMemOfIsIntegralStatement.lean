import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegral
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DiscConductor.discr_mul_mem_of_isIntegral` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDiscrMulMemOfIsIntegral.lean&line=159#L159)
-/
theorem _root_.GlobalTheory.T.exists_ne_zero_mul_integral_eq_tensor : ∀ (T U C : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CharZero T] [CommRing U] [IsDomain U] [IsIntegrallyClosed U] [Algebra T U] [Module.Flat T U] [CommRing C] [IsDomain C] [Algebra T C] [Module.Finite T C], Function.Injective (algebraMap T U) → Function.Injective (algebraMap T C) → ∃ d : T, d ≠ 0 ∧ ∀ c : FractionRing (U ⊗[T] C), IsIntegral (U ⊗[T] C) c → ∃ s : (U ⊗[T] C), algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) s = algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) (algebraMap T (U ⊗[T] C) d) * c := by
  first | exact @GlobalTheory.DiscConductor.discr_mul_mem_of_isIntegral | exact GlobalTheory.DiscConductor.discr_mul_mem_of_isIntegral | (intros; apply GlobalTheory.DiscConductor.discr_mul_mem_of_isIntegral <;> assumption)
