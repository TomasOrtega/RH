import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.LowerInv

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

/- English proof (translation)
Introduce `N Λ H _ _ σ v hU hv hw a`. Establish `hfun : (fun b => Complex.exp ((((Pi.single a (2 * Real.pi) : Fin N → ℝ) b : ℝ) : ℂ) * Complex.I)) = fun _ => (1 : ℂ)`. Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality.

Simplify using `only [Pi.single_eq_same]`. Use `push_cast`. Conclude with `Complex.exp_two_pi_mul_I`. Simplify using `[hb]`. Establish `hmem` using `lowerInv_torus_mem (N := N) (Pi.single a (2 * Real.pi))`.

Establish `h` using `hw (Pi.single a (2 * Real.pi)) hmem`. Rewrite `h` using `[hfun, Matrix.diagonal_one, hU.1.1]`. Establish `hsum : (∑ b, Λ b * (Pi.single a (2 * Real.pi) : Fin N → ℝ) b) = Λ a * (2 * Real.pi)`. Simplify using `[Pi.single_apply]`. Rewrite `h` using `[hsum]`.

Establish `he : Complex.exp (((Λ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1`. Assume the negation of the conclusion as `hne`. Apply `hv` to reduce the goal to its premises. Establish `h2 : (1 - Complex.exp (((Λ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)) • v = 0`. Rewrite using `[sub_smul, one_smul, ← h]`.

Simplify using the standard rewrite rules. Conclude with `(smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hne))`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.mp he`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hpi : (2 * (Real.pi : ℂ)) * Complex.I ≠ 0`.

Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `: (Λ a : ℂ) = (n : ℂ)`. Apply `mul_right_cancel₀ hpi` to reduce the goal to its premises. Move the coercions through the operations in `at hn`. Take the linear combination `hn`.

Conclude with `this` after adjusting the coercions.
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
Introduce `N Λ H _ _ σ S K P hU hstab hPσ v0 hw θ x`. Establish `hwt : σ (torus (-θ)) (v0 : H) = Complex.exp (((∑ a, Λ a * (-θ) a : ℝ) : ℂ) * Complex.I) • (v0 : H)` using `hw (-θ) (lowerInv_torus_mem (-θ))`. Establish `hdet : (torus θ).det = Complex.exp (((∑ a, θ a : ℝ) : ℂ) * Complex.I)`. Rewrite using `[torus, Matrix.det_diagonal]`. Use `push_cast`.

Rewrite using `[Finset.sum_mul, Complex.exp_sum]`. Rewrite using `[Submodule.coe_inner, hPσ (torus θ) (lowerInv_torus_mem θ) x, inner_smul_right, lowerInv_adj hU θ, hwt, inner_smul_left, ← Submodule.coe_inner, hdet, ← Complex.exp_nat_mul, ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]`. Use `congr 2`. Simplify using `only [map_mul, Complex.conj_ofReal, Complex.conj_I]`. Use `push_cast`.

Simplify using `only [Pi.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]`. Put the polynomial expressions in normal form. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Use `push_cast`.

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
