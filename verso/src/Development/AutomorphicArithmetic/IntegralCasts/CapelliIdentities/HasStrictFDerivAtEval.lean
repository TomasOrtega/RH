import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qi29.polyDeriv :
    {n : ℕ} → MvPolynomial (Fin n) ℂ → EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
    fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) ↦
      ∑ l : Fin n,
        (MvPolynomial.eval fun (i : Fin n) ↦ x.ofLp i : MvPolynomial (Fin n) ℂ → ℂ)
            ((MvPolynomial.pderiv l : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ) p) •
          EuclideanSpace.proj l

/- English proof (translation)
Introduce `n p x`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h : UpperTheory.Reformulated.B.Qi29.polyDeriv (MvPolynomial.C a : MvPolynomial (Fin n) ℂ) x = 0`. Simplify using `[UpperTheory.Reformulated.B.Qi29.polyDeriv]`.

Rewrite using `[h]`. Simplify using `only [MvPolynomial.eval_C]`. Conclude with `hasStrictFDerivAt_const a x`. Consider the case `add p q hp hq`. Establish `h : UpperTheory.Reformulated.B.Qi29.polyDeriv (p + q) x = UpperTheory.Reformulated.B.Qi29.polyDeriv p x + UpperTheory.Reformulated.B.Qi29.polyDeriv q x`.

Simplify using `only [UpperTheory.Reformulated.B.Qi29.polyDeriv, map_add, add_smul, Finset.sum_add_distrib]`. Rewrite using `[h]`. Simplify using `only [map_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p i hp`.

Establish `hi : HasStrictFDerivAt (fun y : EuclideanSpace ℂ (Fin n) ↦ y.ofLp i) (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) x` using `(EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).hasStrictFDerivAt`. Establish `h : UpperTheory.Reformulated.B.Qi29.polyDeriv (p * MvPolynomial.X i) x = (MvPolynomial.eval (fun j : Fin n ↦ x.ofLp j) p) • (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) + (x.ofLp i) • UpperTheory.Reformulated.B.Qi29.polyDeriv p x`. Simplify using `only [UpperTheory.Reformulated.B.Qi29.polyDeriv, Derivation.leibniz, smul_eq_mul, map_add, map_mul, MvPolynomial.eval_X, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single i]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[MvPolynomial.pderiv_X_of_ne hb.symm]`. Simplify using the standard rewrite rules. Rewrite using `[h]`.

Simplify using `only [map_mul, MvPolynomial.eval_X]`. Conclude with `hp.mul hi`.
-/
theorem UpperTheory.Reformulated.B.Qi29.hasStrictFDerivAt_eval :
    ∀ {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)),
      HasStrictFDerivAt
        (fun (y : EuclideanSpace ℂ (Fin n)) ↦ (MvPolynomial.eval fun (i : Fin n) ↦ y.ofLp i : MvPolynomial (Fin n) ℂ → ℂ) p)
        (UpperTheory.Reformulated.B.Qi29.polyDeriv p x) x := by
  intro n p x
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (MvPolynomial.C a : MvPolynomial (Fin n) ℂ) x = 0 := by
      simp [UpperTheory.Reformulated.B.Qi29.polyDeriv]
    rw [h]
    simp only [MvPolynomial.eval_C]
    exact hasStrictFDerivAt_const a x
  | add p q hp hq =>
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (p + q) x
        = UpperTheory.Reformulated.B.Qi29.polyDeriv p x + UpperTheory.Reformulated.B.Qi29.polyDeriv q x := by
      simp only [UpperTheory.Reformulated.B.Qi29.polyDeriv, map_add, add_smul, Finset.sum_add_distrib]
    rw [h]
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    have hi : HasStrictFDerivAt (fun y : EuclideanSpace ℂ (Fin n) ↦ y.ofLp i)
        (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) x :=
      (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).hasStrictFDerivAt
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (p * MvPolynomial.X i) x
        = (MvPolynomial.eval (fun j : Fin n ↦ x.ofLp j) p) •
            (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)
          + (x.ofLp i) • UpperTheory.Reformulated.B.Qi29.polyDeriv p x := by
      simp only [UpperTheory.Reformulated.B.Qi29.polyDeriv, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
        MvPolynomial.eval_X, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [MvPolynomial.pderiv_X_of_ne hb.symm]
      · simp
    rw [h]
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul hi
