import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.RingTheory.Polynomial.ScaleRoots

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Simplify using `only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hd : ∑ i ∈ m.support, m i = d`. Use `h (MvPolynomial.mem_support_iff.mp hm)` as an intermediate fact. Rewrite using `[← this, Finsupp.weight_apply, Finsupp.sum]`.

Simplify using the standard rewrite rules. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem eval_smul_homog {σ R : Type} [CommRing R] {φ : MvPolynomial σ R} {d : ℕ}
    (h : φ.IsHomogeneous d) (a : R) (x : σ → R) :
    MvPolynomial.eval₂Hom (RingHom.id R) (fun s => a * x s) φ
      = MvPolynomial.eval₂Hom (RingHom.id R) x φ * a ^ d := by
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := h (MvPolynomial.mem_support_iff.mp hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

/- English proof (translation)
Use `nontriviality R`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.prod_insert hj, mul_scaleRoots', ih, X_sub_C_scaleRoots, mul_comm (x j) a]`.

Rewrite using `[(monic_X_sub_C _).leadingCoeff, (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)).leadingCoeff]`. Simplify using the standard rewrite rules.
-/
private theorem prod_scale {ι R : Type} [CommRing R] (a : R) (x : ι → R) (s : Finset ι) :
    (∏ i ∈ s, (X - C (x i))).scaleRoots a = ∏ i ∈ s, (X - C (a * x i)) := by
  classical
  nontriviality R
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, mul_scaleRoots', ih, X_sub_C_scaleRoots,
      mul_comm (x j) a]
    rw [(monic_X_sub_C _).leadingCoeff,
      (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)).leadingCoeff]
    simp

/- English proof (translation)
Introduce `n R _ a M`. Use `⟨?_, fun x => prod_scale a x _⟩` and prove the remaining obligations. Break down `subsingleton_or_nontrivial R with hR | hR` into its components or cases. Conclude with `Subsingleton.elim _ _`. Use extensionality with `i`.

Rewrite using `[coeff_scaleRoots, Matrix.charpoly_natDegree_eq_dim]`. Break down `le_or_gt i (Fintype.card (Fin n)) with hi | hi` into its components or cases. Establish `h1 : (a • M).charpoly.coeff i = _` using `(Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id R) (fun ij : Fin n × Fin n => a * M ij.1 ij.2) i).symm`. Establish `h2 : M.charpoly.coeff i = _` using `(Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id R) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm`. Rewrite using `[h1, h2]`.

Conclude with `eval_smul_homog (Matrix.charpoly.univ_coeff_isHomogeneous R (Fin n) i _ (Nat.add_sub_cancel' hi)) a _`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (by rwa [Matrix.charpoly_natDegree_eq_dim]), coeff_eq_zero_of_natDegree_lt (by rwa [Matrix.charpoly_natDegree_eq_dim]), zero_mul]`.
-/
theorem UpperTheory.V.Ws.P1.cpSmul :
    ∀ {n : ℕ} {R : Type} [CommRing R] (a : R) (M : Matrix (Fin n) (Fin n) R), (a • M).charpoly = M.charpoly.scaleRoots a ∧
          ∀ x : Fin n → R, (∏ i, (X - C (x i))).scaleRoots a = ∏ i, (X - C (a * x i)) := by
  intro n R _ a M
  refine ⟨?_, fun x => prod_scale a x _⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  ext i
  rw [coeff_scaleRoots, Matrix.charpoly_natDegree_eq_dim]
  rcases le_or_gt i (Fintype.card (Fin n)) with hi | hi
  · have h1 : (a • M).charpoly.coeff i = _ :=
      (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id R)
        (fun ij : Fin n × Fin n => a * M ij.1 ij.2) i).symm
    have h2 : M.charpoly.coeff i = _ :=
      (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id R)
        (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
    rw [h1, h2]
    exact eval_smul_homog
      (Matrix.charpoly.univ_coeff_isHomogeneous R (Fin n) i _ (Nat.add_sub_cancel' hi)) a _
  · rw [coeff_eq_zero_of_natDegree_lt (by rwa [Matrix.charpoly_natDegree_eq_dim]),
      coeff_eq_zero_of_natDegree_lt (by rwa [Matrix.charpoly_natDegree_eq_dim]), zero_mul]
