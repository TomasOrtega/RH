import ReciprocityTheory.DualLattices.WtGtRowSubstXSub

noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

/- English proof (translation)
Introduce `h0`. Establish `hsum : fischer P P = ((∑ A ∈ P.support, ‖coeff A P‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) : ℝ) : ℂ)`. Unfold `fischer`. Rewrite using `[Finset.union_self]`. Use `push_cast`.

Use `Finset.sum_congr rfl fun A _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Simplify using `only [Finsupp.prod]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hne : P.support.Nonempty` using `Finset.nonempty_iff_ne_empty.mpr (fun h => hP (MvPolynomial.support_eq_empty.mp h))`. Establish `hpos : 0 < ∑ A ∈ P.support, ‖coeff A P‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ)`. Use `Finset.sum_pos (fun A hA => ?_) hne` and prove the remaining obligations. Establish `h1 : coeff A P ≠ 0` using `MvPolynomial.mem_support_iff.mp hA`. Establish `h2 : 0 < ((A.prod fun _ e => e.factorial : ℕ) : ℝ)`.

Conclude with `Finset.prod_pos fun _ _ => Nat.factorial_pos _` after adjusting the coercions. Establish `h3 : 0 < ‖coeff A P‖ ^ 2` using `by positivity`. Check the signs of the components of the expression. Rewrite `h0` using `[hsum]`. Establish `h4 : (∑ A ∈ P.support, ‖coeff A P‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) : ℝ) = 0`.

Conclude with `h0` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fischer_self_ne_zero (P : MvPolynomial (Fin ν × ι) ℂ) (hP : P ≠ 0) : fischer P P ≠ 0 := by
  intro h0
  have hsum : fischer P P = ((∑ A ∈ P.support,
      ‖coeff A P‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    unfold fischer
    rw [Finset.union_self]
    push_cast
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [Finsupp.prod]
    push_cast
    ring
  have hne : P.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun h => hP (MvPolynomial.support_eq_empty.mp h))
  have hpos : 0 < ∑ A ∈ P.support, ‖coeff A P‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) := by
    refine Finset.sum_pos (fun A hA => ?_) hne
    have h1 : coeff A P ≠ 0 := MvPolynomial.mem_support_iff.mp hA
    have h2 : 0 < ((A.prod fun _ e => e.factorial : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos fun _ _ => Nat.factorial_pos _
    have h3 : 0 < ‖coeff A P‖ ^ 2 := by positivity
    positivity
  rw [hsum] at h0
  have h4 : (∑ A ∈ P.support, ‖coeff A P‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) : ℝ) = 0 := by
    exact_mod_cast h0
  linarith

/- English proof (translation)
Establish `key : (rowSubst (ι` using `ι) h).comp (rowSubst g) = rowSubst (h * g) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`. Simplify using `only [AlgHom.comp_apply, rowSubst, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, MvPolynomial.C_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Conclude with `congrArg (fun F => F P) key`.
-/
theorem rowSubst_mul (g h : Matrix (Fin ν) (Fin ν) ℂ) (P : MvPolynomial (Fin ν × ι) ℂ) :
    rowSubst h (rowSubst g P) = rowSubst (h * g) P := by
  have key : (rowSubst (ι := ι) h).comp (rowSubst g) = rowSubst (h * g) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, rowSubst, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, MvPolynomial.C_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  exact congrArg (fun F => F P) key

/- English proof (translation)
Establish `h : (fun p : Fin ν × ι => ∑ l, C ((1 : Matrix (Fin ν) (Fin ν) ℂ) l p.1) * X (l, p.2)) = X`. Use function extensionality and compare the values at `p`. Rewrite using `[Finset.sum_eq_single p.1]`. Simplify using the standard rewrite rules. Introduce `l _ hl`.

Simplify using `[Matrix.one_apply_ne hl]`. Simplify using the standard rewrite rules. Unfold `rowSubst`. Rewrite using `[h, MvPolynomial.aeval_X_left_apply]`.
-/
theorem rowSubst_one (P : MvPolynomial (Fin ν × ι) ℂ) : rowSubst (1 : Matrix (Fin ν) (Fin ν) ℂ) P = P := by
  have h : (fun p : Fin ν × ι => ∑ l, C ((1 : Matrix (Fin ν) (Fin ν) ℂ) l p.1) * X (l, p.2)) = X := by
    funext p
    rw [Finset.sum_eq_single p.1]
    · simp
    · intro l _ hl
      simp [Matrix.one_apply_ne hl]
    · simp
  unfold rowSubst
  rw [h, MvPolynomial.aeval_X_left_apply]

end ReciprocityTheory.PGsh
