import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegerOfMaximalIdealPowSmulIsInteger
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsIntegerOfMaximalIdealPowSmulIsInteger.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.isInteger_of_maximalIdeal_pow_smul_isInteger' : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S → ∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ maximalIdeal S ^ k, IsLocalization.IsInteger S (a • c)) → IsLocalization.IsInteger S c := by
  first | exact @GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger | exact GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger | (intros; apply GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger <;> assumption)
