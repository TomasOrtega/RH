import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas

open MvPolynomial Formalism.REAL

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on generalizing g`. Name the introduced variables `a`. Rewrite using `[LFocks_sub_C, LFocks_C_left, LFocks_C_left, LFocks_constantCoeff_sub]`. Name the introduced variables `p q hp hq`. Rewrite using `[map_add, Formalism.REAL.fischerInner_add_left, Formalism.REAL.fischerInner_add_left, hp, hq]`.

Name the introduced variables `p i hp`. Rewrite using `[map_mul, LFocks_sub_X, mul_comm p (X i), Formalism.REAL.fischerInner_X_mul_left i p, LFocks_pderiv_sub, Formalism.REAL.fischerInner_sum_right, Finset.mul_sum, Formalism.REAL.fischerInner_sum_left]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[LFocks_C_mul_right, ← hp, Matrix.conjTranspose_apply, star_star, mul_comm (sub U p), mul_assoc, LFocks_C_mul_left, Formalism.REAL.fischerInner_X_mul_left]`.
-/
lemma LFocks_subAdj {σ : Type*} [Fintype σ] [DecidableEq σ] (U : Matrix σ σ ℂ)
    (f g : MvPolynomial σ ℂ) :
    fockF (sub U f) g = fockF f (sub U.conjTranspose g) := by
  induction f using MvPolynomial.induction_on generalizing g
  · rename_i a
    rw [LFocks_sub_C, LFocks_C_left, LFocks_C_left,
      LFocks_constantCoeff_sub]
  · rename_i p q hp hq
    rw [map_add, Formalism.REAL.fischerInner_add_left, Formalism.REAL.fischerInner_add_left, hp, hq]
  · rename_i p i hp
    rw [map_mul, LFocks_sub_X, mul_comm p (X i), Formalism.REAL.fischerInner_X_mul_left i p,
      LFocks_pderiv_sub, Formalism.REAL.fischerInner_sum_right, Finset.mul_sum, Formalism.REAL.fischerInner_sum_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LFocks_C_mul_right, ← hp, Matrix.conjTranspose_apply, star_star,
      mul_comm (sub U p), mul_assoc, LFocks_C_mul_left,
      Formalism.REAL.fischerInner_X_mul_left]

/- English proof (translation)
Introduce `_ _ _ U f g` and use `LFocks_subAdj U f g`.
-/
theorem fischerInnerSubstitutionAdjoint : FockSubAdj :=
  fun _ _ _ U f g => LFocks_subAdj U f g

end Formalism.GradedWeylDivisibility
