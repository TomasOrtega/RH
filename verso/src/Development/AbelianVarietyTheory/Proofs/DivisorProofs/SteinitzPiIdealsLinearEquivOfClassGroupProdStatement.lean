import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinitzPiIdealsLinearEquivOfClassGroupProd
import Mathlib
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SteinitzProd.steinitz` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSteinitzPiIdealsLinearEquivOfClassGroupProd.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.steinitz_pi_ideals_linearEquiv_of_classGroup_prod : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι] (I J : ι → (Ideal R)⁰), ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) → Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R))) := by
  first | exact @GlobalTheory.SteinitzProd.steinitz | exact GlobalTheory.SteinitzProd.steinitz | (intros; apply GlobalTheory.SteinitzProd.steinitz <;> assumption)
