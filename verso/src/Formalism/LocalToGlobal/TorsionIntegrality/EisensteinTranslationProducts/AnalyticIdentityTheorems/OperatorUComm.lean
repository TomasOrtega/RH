import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroLogDerivative

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace OperatorUThetaLemmas

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
lemma conj_herm (L : PeriodPair) (x y : ℂ) : conj (herm L x y) = herm L y x := by
  simp only [Formalism.L2.Th1.F.herm, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_sub_herm (L : PeriodPair) (x y : ℂ) :
    herm L x y - herm L y x = 2 * Complex.I * (altE L x y : ℂ) := by
  rw [← conj_herm L x y, Complex.sub_conj]
  simp only [Formalism.L2.Th1.F.altE]
  push_cast
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_add_left (L : PeriodPair) (x y w : ℂ) :
    herm L (x + y) w = herm L x w + herm L y w := by
  simp only [Formalism.L2.Th1.F.herm]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_add_right (L : PeriodPair) (w x y : ℂ) :
    herm L w (x + y) = herm L w x + herm L w y := by
  simp only [Formalism.L2.Th1.F.herm, map_add]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
lemma altE_swap (L : PeriodPair) (x y : ℂ) : altE L y x = -altE L x y := by
  simp only [Formalism.L2.Th1.F.altE]
  rw [← conj_herm L x y, Complex.conj_im]

end OperatorUThetaLemmas

open OperatorUThetaLemmas

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem mul_exp_mul_exp_eq_exp_mul_of_add_eq (f a b c d : ℂ) (h : a + b = c + d) :
    f * Complex.exp a * Complex.exp b = Complex.exp c * (f * Complex.exp d) := by
  rw [mul_assoc, ← Complex.exp_add, h, Complex.exp_add]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Take a linear combination of the given relations to obtain the conclusion.
-/
theorem operator_u_mul : OpUMul := by
  intro L x y F z
  simp only [opU]
  rw [add_assoc z x y]
  apply mul_exp_mul_exp_eq_exp_mul_of_add_eq
  simp only [Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_add_left, Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_add_right]
  linear_combination (-(Real.pi : ℂ) / 2) * Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_sub_herm L x y

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem operator_u_comm : OpUComm := by
  intro L F z
  refine ⟨by simp [opU, herm], fun x y => ?_⟩
  rw [operator_u_mul L x y F z, operator_u_mul L y x F z, add_comm y x,
    Formalism.L2.Th1.F.OperatorUThetaLemmas.altE_swap L x y, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Formalism.L2.Th1.F
