import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.LowerInv

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem lambda_integrality : LamInt := by
  intro N Λ H _ _ σ v hU hv hw a
  have hfun : (fun b => Complex.exp ((((Pi.single a (2 * Real.pi) : Fin N → ℝ) b : ℝ) : ℂ) * Complex.I))
      = fun _ => (1 : ℂ) := by
    funext b
    by_cases hb : b = a
    · subst hb
      simp only [Pi.single_eq_same]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · simp [hb]
  have hmem := lowerInv_torus_mem (N := N) (Pi.single a (2 * Real.pi))
  have h := hw (Pi.single a (2 * Real.pi)) hmem
  rw [hfun, Matrix.diagonal_one, hU.1.1] at h
  have hsum : (∑ b, Λ b * (Pi.single a (2 * Real.pi) : Fin N → ℝ) b) = Λ a * (2 * Real.pi) := by
    simp [Pi.single_apply]
  rw [hsum] at h
  have he : Complex.exp (((Λ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := by
    by_contra hne
    apply hv
    have h2 : (1 - Complex.exp (((Λ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)) • v = 0 := by
      rw [sub_smul, one_smul, ← h]
      simp
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  refine ⟨n, ?_⟩
  have hpi : (2 * (Real.pi : ℂ)) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (Λ a : ℂ) = (n : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast at hn
    linear_combination hn
  exact_mod_cast this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations.

Simplify using the standard rewrite rules. Put the polynomial expressions in normal form. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem torus_eigenvalue_formula : TorusEig := by
  intro N Λ H _ _ σ S K P hU hstab hPσ v0 hw θ x
  have hwt : σ (torus (-θ)) (v0 : H) =
      Complex.exp (((∑ a, Λ a * (-θ) a : ℝ) : ℂ) * Complex.I) • (v0 : H) :=
    hw (-θ) (lowerInv_torus_mem (-θ))
  have hdet : (torus θ).det = Complex.exp (((∑ a, θ a : ℝ) : ℂ) * Complex.I) := by
    rw [torus, Matrix.det_diagonal]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
  rw [Submodule.coe_inner, hPσ (torus θ) (lowerInv_torus_mem θ) x, inner_smul_right,
    lowerInv_adj hU θ, hwt, inner_smul_left, ← Submodule.coe_inner, hdet, ← Complex.exp_nat_mul,
    ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  simp only [Pi.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  ring_nf
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

end PI.WMI
