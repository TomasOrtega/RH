import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularOfEtalePuncturedOfDepthPosDomain
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsSMulRegularOfEtalePuncturedOfDepthPosDomain.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos_domain' : ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsDomain S] (A : Type) [CommRing A] [Algebra S A], ReciprocityTheory.CA.ModDepthGE S A 1 → (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) → ∀ s : S, s ≠ 0 → IsSMulRegular A s := by
  first | exact @GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos_domain | exact GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos_domain | (intros; apply GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos_domain <;> assumption)
