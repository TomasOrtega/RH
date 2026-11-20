import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoOfRegularQuotientNoSocle
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.modDepthGE_two_of_isSMulRegular_of_quotSMulTop` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FModDepthGETwoOfRegularQuotientNoSocle.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.modDepthGE_two_of_regular_quotient_no_socle : ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (M : Type) [AddCommGroup M] [Module S M] [Module.Finite S M] [Nontrivial M] (x : S), x ∈ maximalIdeal S → IsSMulRegular M x → (∀ u : M, (∀ a ∈ maximalIdeal S, a • u ∈ x • (⊤ : Submodule S M)) → u ∈ x • (⊤ : Submodule S M)) → ReciprocityTheory.CA.ModDepthGE S M 2 := by
  first | exact @GlobalTheory.modDepthGE_two_of_isSMulRegular_of_quotSMulTop | exact GlobalTheory.modDepthGE_two_of_isSMulRegular_of_quotSMulTop | (intros; apply GlobalTheory.modDepthGE_two_of_isSMulRegular_of_quotSMulTop <;> assumption)
