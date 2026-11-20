import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

/- English proof (translation)
Introduce `hT hM`. Prove the components needed by the constructor for the conclusion. Introduce `R _ _ n lam g y`. Simplify using `only [hT R]`. Establish `h` using `hM R n (Matrix.of fun a j => g j ^ shift lam a) (fun a => y ^ shift lam a) (fun _ => 1)`.

Simplify using `only [Matrix.of_apply, prod_const_one, mul_one] at h`. Combine the equalities or inequalities in the displayed calculation. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Unfold `altn`. Use `congr 1`.

Use extensionality with `a j`. Simplify using `only [Matrix.of_apply, scaleAt]`. Apply the tactic sequence `split_ifs <;> simp [mul_pow]`. Use `_ = _ := by`. Rewrite using `[h]`.

Simplify using `only [altn, shift]`. Expand and normalize the polynomial expressions, which then agree. Introduce `R _ _ n lam g y`. Simplify using `only [hT R]`. Establish `h` using `hM R n (Matrix.of fun a j => g j ^ shift lam a) (fun _ => 1) (fun a => y ^ shift lam a)`.

Simplify using `only [Matrix.of_apply, one_mul, prod_pow_eq_pow_sum] at h`. Combine the equalities or inequalities in the displayed calculation. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Unfold `altn`. Use `congr 1`.

Use extensionality with `a j`. Simplify using `only [Matrix.of_apply, scaleOff]`. Apply the tactic sequence `split_ifs <;> simp [mul_pow]`. Use `_ = _ := by`. Rewrite using `[h]`.

Simplify using `only [altn, shift]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem schurYClr_of : Comparison₂ → MixDet → SchurYClr ∧ SchurYOffClr := by
  intro hT hM
  constructor
  · intro R _ _ n lam g y
    simp only [hT R]
    have h := hM R n (Matrix.of fun a j => g j ^ shift lam a) (fun a => y ^ shift lam a) (fun _ => 1)
    simp only [Matrix.of_apply, prod_const_one, mul_one] at h
    calc ∑ i, altn (shift lam) (scaleAt y i g)
        = ∑ i, (Matrix.of fun a j => (if j = i then y ^ shift lam a else 1) * g j ^ shift lam a).det := by
          refine sum_congr rfl fun i _ => ?_
          unfold altn
          congr 1
          ext a j
          simp only [Matrix.of_apply, scaleAt]
          split_ifs <;> simp [mul_pow]
      _ = _ := by
          rw [h]
          simp only [altn, shift]
          ring
  · intro R _ _ n lam g y
    simp only [hT R]
    have h := hM R n (Matrix.of fun a j => g j ^ shift lam a) (fun _ => 1) (fun a => y ^ shift lam a)
    simp only [Matrix.of_apply, one_mul, prod_pow_eq_pow_sum] at h
    calc ∑ i, altn (shift lam) (scaleOff y i g)
        = ∑ i, (Matrix.of fun a j => (if j = i then 1 else y ^ shift lam a) * g j ^ shift lam a).det := by
          refine sum_congr rfl fun i _ => ?_
          unfold altn
          congr 1
          ext a j
          simp only [Matrix.of_apply, scaleOff]
          split_ifs <;> simp [mul_pow]
      _ = _ := by
          rw [h]
          simp only [altn, shift]
          ring

end UpperTheory.Gal.Schur
