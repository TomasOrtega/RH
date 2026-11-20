import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenEval

open Polynomial UpperTheory.V.W

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Establish `h : MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X])) (MvPolynomial.monomial u a) = C (MvPolynomial.monomial u a) * X ^ u.degree`. Rewrite using `[MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, Finsupp.prod, Finsupp.prod, show u.degree = ∑ i ∈ u.support, u i from rfl]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod, Finset.prod_pow_eq_pow_sum, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial, MvPolynomial.coeff_monomial]`. Use `split_ifs with h1 h2 h2`. Rewrite using `[MvPolynomial.coeff_monomial, if_pos h2]`. Rewrite using `[MvPolynomial.coeff_monomial, if_neg h2]`.

Conclude with `absurd (congrArg Finsupp.degree h2) h1`. Rewrite using `[MvPolynomial.coeff_zero]`. Consider the case `add p q hp hq`. Rewrite using `[map_add, Polynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]`.
-/
private theorem coeff_scale {A : Type} [CommRing A] {m : ℕ} (P : MvPolynomial (Fin m) A) (s : Fin m →₀ ℕ) :
    MvPolynomial.coeff s
      ((MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X])) P).coeff s.degree)
      = MvPolynomial.coeff s P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have h : MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
        (MvPolynomial.monomial u a) = C (MvPolynomial.monomial u a) * X ^ u.degree := by
      rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, Finsupp.prod, Finsupp.prod,
        show u.degree = ∑ i ∈ u.support, u i from rfl]
      simp only [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod, Finset.prod_pow_eq_pow_sum,
        Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul]
      ring
    rw [h, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · rw [MvPolynomial.coeff_monomial, if_pos h2]
    · rw [MvPolynomial.coeff_monomial, if_neg h2]
    · exact absurd (congrArg Finsupp.degree h2) h1
    · rw [MvPolynomial.coeff_zero]
  | add p q hp hq =>
    rw [map_add, Polynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]

/- English proof (translation)
Introduce `n A G _ _ D m y`. Establish `hφ : (MvPolynomial.aeval (fun j => (C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))) = (Polynomial.CAlgHom : MvPolynomial (Fin m) A →ₐ[A] (MvPolynomial (Fin m) A)[X])` using `MvPolynomial.algHom_ext fun i => by simp [Polynomial.CAlgHom]`. Establish `hC : MvPolynomial.aeval (fun j => (C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X])) (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) = C (D.D (MvPolynomial (Fin m) A) (GDet.gen y))`. Rewrite using `[hφ]`. Both sides reduce to the same expression.

Establish `key : MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X])) (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) = X ^ n * C (D.D (MvPolynomial (Fin m) A) (GDet.gen y))`. Rewrite using `[← UpperTheory.V.AlgebraTools.Det.genEval D _ m y, ← hC, ← UpperTheory.V.AlgebraTools.Det.genEval D _ m y, ← D.homog, Finset.smul_sum]`. Simplify using `only [mul_smul]`. Introduce `d hd`. Establish `h1` using `coeff_scale (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) d`.

Rewrite `h1` using `[key, mul_comm, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]`. Establish `hw : Finsupp.weight 1 d = d.degree`. Simplify using `only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one]`. Both sides reduce to the same expression. Rewrite using `[hw]`.

Assume the negation of the conclusion as `hne`. Rewrite `h1` using `[if_neg (Ne.symm hne), MvPolynomial.coeff_zero]`. Conclude with `hd h1.symm`.
-/
theorem UpperTheory.V.AlgebraTools.Det.genHomog :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (m : ℕ) (y : Fin m → MonoidAlgebra A G),
    (D.D (MvPolynomial (Fin m) A) (GDet.gen y)).IsHomogeneous n := by
  intro n A G _ _ D m y
  have hφ : (MvPolynomial.aeval (fun j => (C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))) =
      (Polynomial.CAlgHom : MvPolynomial (Fin m) A →ₐ[A] (MvPolynomial (Fin m) A)[X]) :=
    MvPolynomial.algHom_ext fun i => by simp [Polynomial.CAlgHom]
  have hC : MvPolynomial.aeval (fun j => (C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
      (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) = C (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
    rw [hφ]
    rfl
  have key : MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
      (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) = X ^ n * C (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
    rw [← UpperTheory.V.AlgebraTools.Det.genEval D _ m y, ← hC, ← UpperTheory.V.AlgebraTools.Det.genEval D _ m y, ← D.homog,
      Finset.smul_sum]
    simp only [mul_smul]
  intro d hd
  have h1 := coeff_scale (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) d
  rw [key, mul_comm, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial] at h1
  have hw : Finsupp.weight 1 d = d.degree := by
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  rw [hw]
  by_contra hne
  rw [if_neg (Ne.symm hne), MvPolynomial.coeff_zero] at h1
  exact hd h1.symm
