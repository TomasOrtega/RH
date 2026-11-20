import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepTwo
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem twistMul_twist_twistMul {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (M : SubSystem S x Ω) (a a' : ℕ) (c c' : ℤ) :
    (twistMul M a c).twist (twistMul M a' c') = twistMul M (a + a') (c + c') := by
  refine SubSystem.ext_sub fun I => ?_
  rw [SubSystem.twist_sub_eq_mul_of_line, twistMul_sub, twistMul_sub, twistMul_sub, pow_add,
    ← twistSys_sub_mul]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree. Move the embeddings inside the algebraic operations.

Take a linear combination of the given relations to obtain the conclusion.
-/
theorem TwistAlg.proof : TwistAlg.Statement.{u, w} := by
  intro S _ Ω _ _ N x M p q m m' b₁ b₂ h
  rw [pow_twistMul, pow_twistMul, pow_twistMul, twistMul_twist_twistMul]
  congr 1
  · ring
  · push_cast
    linear_combination (b₁ : ℤ) * h

end

end GroundTheory.Heights₂.Heights.Kleiman
