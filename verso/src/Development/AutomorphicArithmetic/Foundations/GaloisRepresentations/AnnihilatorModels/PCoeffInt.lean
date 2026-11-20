import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `R T _ _ _ ι I _ _ c hc a m`. Set `c' : I → ι → integralClosure R T` to `fun i k => ⟨c i k, hc i k⟩`. Set `f : MvPolynomial ι (integralClosure R T) →+* MvPolynomial ι T` to `MvPolynomial.map (algebraMap (integralClosure R T) T)`. Establish `hform : ∀ i, form (c i) = (form (c' i)).map f`. Introduce `i`.

Simplify using `[form, f, Polynomial.map_sub, MvPolynomial.map_C, c']`. Rewrite using `[Polynomial.map_sum]`. Simplify using `[Polynomial.map_mul, Polynomial.map_C, MvPolynomial.map_C, MvPolynomial.map_X]`. Establish `hP : (∏ i, form (c i)) = (∏ i, form (c' i)).map f`. Rewrite using `[Polynomial.map_prod]`.

Conclude with `Finset.prod_congr rfl fun i _ => hform i`. Rewrite using `[hP, Polynomial.coeff_map]`. Simplify using `only [f, MvPolynomial.coeff_map]`. Conclude with `(((∏ i, form (c' i)).coeff a).coeff m).2`.
-/
theorem UpperTheory.Gal.crystallineComparison.coeffInt_of :
    CoeffInt := by
  intro R T _ _ _ ι I _ _ c hc a m
  let c' : I → ι → integralClosure R T := fun i k => ⟨c i k, hc i k⟩
  let f : MvPolynomial ι (integralClosure R T) →+* MvPolynomial ι T :=
    MvPolynomial.map (algebraMap (integralClosure R T) T)
  have hform : ∀ i, form (c i) = (form (c' i)).map f := by
    intro i
    simp [form, f, Polynomial.map_sub, MvPolynomial.map_C, c']
    rw [Polynomial.map_sum]
    simp [Polynomial.map_mul, Polynomial.map_C, MvPolynomial.map_C, MvPolynomial.map_X]
  have hP : (∏ i, form (c i)) = (∏ i, form (c' i)).map f := by
    rw [Polynomial.map_prod]
    exact Finset.prod_congr rfl fun i _ => hform i
  rw [hP, Polynomial.coeff_map]
  simp only [f, MvPolynomial.coeff_map]
  exact (((∏ i, form (c' i)).coeff a).coeff m).2
