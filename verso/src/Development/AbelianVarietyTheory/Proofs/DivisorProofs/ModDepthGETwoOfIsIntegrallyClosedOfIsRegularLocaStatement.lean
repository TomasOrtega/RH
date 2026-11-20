import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoOfIsIntegrallyClosedOfIsRegularLoca
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FModDepthGETwoOfIsIntegrallyClosedOfIsRegularLoca.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing' : ∀ (R A : Type) [CommRing R] [IsRegularLocalRing R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], 2 ≤ ringKrullDim R → ReciprocityTheory.CA.ModDepthGE R A 2 := by
  first | exact @GlobalTheory.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing | exact GlobalTheory.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing | (intros; apply GlobalTheory.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing <;> assumption)
