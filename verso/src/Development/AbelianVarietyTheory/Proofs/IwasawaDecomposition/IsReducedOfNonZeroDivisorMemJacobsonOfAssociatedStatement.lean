import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsReducedOfNonZeroDivisorMemJacobsonOfAssociated
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsReducedOfNonZeroDivisorMemJacobsonOfAssociated.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.isReduced_of_nonZeroDivisor_mem_jacobson_of_assocPrimes : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R → x ∈ Ideal.jacobson (⊥ : Ideal R) → (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) → IsDomain (Localization.AtPrime P)) → IsReduced R := by
  first | exact @GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes | exact GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes | (intros; apply GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes <;> assumption)
