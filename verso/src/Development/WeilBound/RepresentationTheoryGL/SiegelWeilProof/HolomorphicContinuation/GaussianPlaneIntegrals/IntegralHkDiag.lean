import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt

noncomputable section

open MeasureTheory Complex Module
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof

def e1 (z : ℂ) : ℂ := Complex.exp (((-(‖z‖ ^ 2)) : ℝ) : ℂ)

def hk (k l : ℕ) (z : ℂ) : ℂ := z ^ k * star z ^ l * e1 z

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem continuous_hk (k l : ℕ) : Continuous (hk k l) := by
  unfold hk e1
  fun_prop

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem norm_hk (k l : ℕ) (z : ℂ) : ‖hk k l z‖ = ‖z‖ ^ (k + l) * Real.exp (-(‖z‖ ^ 2)) := by
  simp only [hk, e1, norm_mul, norm_pow, norm_star, Complex.norm_exp_ofReal, pow_add]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Put the expressions in a common number system so they can be compared.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pow_exp_le (n : ℕ) : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    t ^ n * Real.exp (-(t ^ 2)) ≤ C * (1 + t) ^ (-(3 : ℝ)) := by
  refine ⟨((n + 3).factorial : ℝ) * Real.exp 2, fun t ht => ?_⟩
  have h1 : 0 < 1 + t := by linarith
  have hr : (1 + t) ^ (-(3 : ℝ)) = ((1 + t) ^ 3)⁻¹ := by
    rw [Real.rpow_neg h1.le]
    norm_cast
  rw [hr, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hA : t ^ n ≤ (1 + t) ^ n := pow_le_pow_left₀ ht (by linarith) n
  have hB : (1 + t) ^ (n + 3) ≤ ((n + 3).factorial : ℝ) * Real.exp (1 + t) := by
    have h := Real.pow_div_factorial_le_exp (1 + t) h1.le (n + 3)
    rwa [div_le_iff₀ (by positivity), mul_comm] at h
  have hC : Real.exp (1 + t) * Real.exp (-(t ^ 2)) ≤ Real.exp 2 := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (t - 1 / 2)])
  calc t ^ n * Real.exp (-(t ^ 2)) * (1 + t) ^ 3
      ≤ (1 + t) ^ n * Real.exp (-(t ^ 2)) * (1 + t) ^ 3 := by gcongr
    _ = (1 + t) ^ (n + 3) * Real.exp (-(t ^ 2)) := by ring
    _ ≤ ((n + 3).factorial : ℝ) * Real.exp (1 + t) * Real.exp (-(t ^ 2)) := by gcongr
    _ ≤ ((n + 3).factorial : ℝ) * Real.exp 2 := by
      rw [mul_assoc]
      gcongr

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem integrable_hk (k l : ℕ) : Integrable (hk k l) := by
  obtain ⟨C, hC⟩ := pow_exp_le (k + l)
  have hi : Integrable (fun z : ℂ => (1 + ‖z‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by norm_num [finrank_real_complex])
  refine (hi.const_mul C).mono' (continuous_hk k l).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [norm_hk]
  exact hC _ (norm_nonneg _)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts.

Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem integral_hk_ne (k l : ℕ) (h : k ≠ l) : ∫ z, hk k l z = 0 := by
  have hkl : ((k : ℂ) - l) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
  set θ : ℝ := Real.pi / ((k : ℝ) - l) with hθ
  have hfac : Complex.exp (θ * I) ^ k * star (Complex.exp (θ * I)) ^ l = -1 := by
    have hs : star (Complex.exp (θ * I)) = Complex.exp (-(θ * I)) := by
      rw [Complex.star_def, ← Complex.exp_conj]
      simp
    rw [hs, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have h2 : (θ : ℂ) * ((k : ℂ) - l) = Real.pi := by
      rw [hθ]
      push_cast
      field_simp
    have h3 : (k : ℂ) * (θ * I) + l * (-(θ * I)) = Real.pi * I := by
      linear_combination I * h2
    rw [h3, Complex.exp_pi_mul_I]
  have hrot : ∀ z : ℂ, hk k l (Complex.exp (θ * I) * z) = -hk k l z := by
    intro z
    have he : e1 (Complex.exp (θ * I) * z) = e1 z := by
      simp only [e1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    simp only [hk]
    rw [he, star_mul', mul_pow, mul_pow]
    calc Complex.exp (θ * I) ^ k * z ^ k * (star (Complex.exp (θ * I)) ^ l * star z ^ l) * e1 z
        = (Complex.exp (θ * I) ^ k * star (Complex.exp (θ * I)) ^ l) * (z ^ k * star z ^ l * e1 z) := by ring
      _ = -(z ^ k * star z ^ l * e1 z) := by rw [hfac]; ring
  have key := (rotation (Circle.exp θ)).measurePreserving.integral_comp
    (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding (hk k l)
  simp only [LinearIsometryEquiv.coe_toHomeomorph, rotation_apply, Circle.coe_exp, hrot, integral_neg] at key
  linear_combination (-1 / 2 : ℂ) * key

def jr (k : ℕ) : ℝ := ∫ z : ℂ, (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2))

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hk_diag (k : ℕ) (z : ℂ) : hk k k z = (((‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2)) : ℝ) : ℂ) := by
  simp only [hk, e1]
  rw [← mul_pow, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/- English proof (translation)
Rewrite the conclusion repeatedly using the stated equalities. A detailed English derivation is pending.
-/
theorem integral_hk_diag (k : ℕ) : ∫ z, hk k k z = (jr k : ℂ) := by
  simp_rw [hk_diag]
  exact integral_ofReal

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem jr_pos (k : ℕ) : 0 < jr k := by
  have hint : Integrable (fun z : ℂ => (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2))) := by
    refine (integrable_hk k k).norm.congr (ae_of_all _ fun z => ?_)
    simp only [norm_hk]
    ring
  have hnn : 0 ≤ fun z : ℂ => (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2)) := fun z => by positivity
  unfold jr
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hc : Continuous fun z : ℂ => (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2)) := by fun_prop
  exact hc.isOpen_support.measure_pos volume ⟨1, by simp⟩

end PositivityTheory.Rg.Sw.FFTSteps.PosProof
