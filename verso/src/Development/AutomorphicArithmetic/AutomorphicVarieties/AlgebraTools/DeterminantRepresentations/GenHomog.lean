import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenEval

open Polynomial UpperTheory.V.W

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
