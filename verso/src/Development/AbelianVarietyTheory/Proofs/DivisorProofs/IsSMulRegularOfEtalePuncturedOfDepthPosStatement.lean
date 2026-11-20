import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularOfEtalePuncturedOfDepthPos
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsSMulRegularOfEtalePuncturedOfDepthPos.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos' : ∀ (R A : Type) [CommRing R] [IsRegularLocalRing R] [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 1 → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ f : R, f ≠ 0 → IsSMulRegular A f := by
  first | exact @GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos | exact GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos | (intros; apply GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos <;> assumption)
