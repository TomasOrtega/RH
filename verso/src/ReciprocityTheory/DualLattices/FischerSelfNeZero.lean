import ReciprocityTheory.DualLattices.WtGtRowSubstXSub

noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Check the signs of the components of the expression. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
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
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
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
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
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
