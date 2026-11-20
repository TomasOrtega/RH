import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution
import Formalism.LogVandermondeBounds.LogVandermondeProofs.GammaIntegralPolynomialBound

namespace Formalism.HermitianLattices.TraceIntegrality

open MeasureTheory Finset

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Clear the denominators using the available nonvanishing facts. Rewrite the indicated hypotheses repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma fock_real_integral (Om : ℝ) (hOm : 0 < Om) (k : ℕ) :
    ∫ z : ℂ, ‖z‖ ^ k * Real.exp (-‖z‖ ^ 2 / Om) =
      Real.pi * Om ^ ((k : ℝ) / 2 + 1) * Real.Gamma ((k : ℝ) / 2 + 1) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := k) (b := Om⁻¹)
    (by norm_num) (by linarith) (inv_pos.mpr hOm)
  have e : ∀ z : ℂ, ‖z‖ ^ (k : ℝ) * Real.exp (-Om⁻¹ * ‖z‖ ^ (2 : ℝ)) =
      ‖z‖ ^ k * Real.exp (-‖z‖ ^ 2 / Om) := by
    intro z
    rw [Real.rpow_natCast, Real.rpow_two]
    congr 2
    field_simp
  simp_rw [e] at h
  rw [h, Real.inv_rpow hOm.le, ← Real.rpow_neg hOm.le]
  have h1 : -(-((k : ℝ) + 2) / 2) = (k : ℝ) / 2 + 1 := by ring
  have h2 : ((k : ℝ) + 2) / 2 = (k : ℝ) / 2 + 1 := by ring
  rw [h1, h2]
  ring

/- English proof (translation)
Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma fock_real_integrable (Om : ℝ) (hOm : 0 < Om) (k : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ k * Real.exp (-‖z‖ ^ 2 / Om)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  by_contra hn
  have h0 := integral_undef hn
  rw [fock_real_integral Om hOm k] at h0
  have : 0 < Real.pi * Om ^ ((k : ℝ) / 2 + 1) * Real.Gamma ((k : ℝ) / 2 + 1) := by
    have := Real.Gamma_pos_of_pos (s := (k : ℝ) / 2 + 1) (by positivity)
    have := Real.rpow_pos_of_pos hOm ((k : ℝ) / 2 + 1)
    have := Real.pi_pos
    positivity
  linarith

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
private lemma fock_integrable (Om : ℝ) (hOm : 0 < Om) (p q : ℕ) :
    Integrable
      (fun z : ℂ => z ^ p * (starRingEnd ℂ z) ^ q * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ)) := by
  refine (fock_real_integrable Om hOm (p + q)).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · refine Filter.Eventually.of_forall (fun z => ?_)
    rw [norm_mul, norm_mul, norm_pow, norm_pow, RCLike.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_add]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
private lemma fock_rotate (Om : ℝ) (p q : ℕ) (c : Circle) :
    ∫ z : ℂ, z ^ p * (starRingEnd ℂ z) ^ q * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ) =
      ((c : ℂ) ^ p * (starRingEnd ℂ (c : ℂ)) ^ q) *
        ∫ z : ℂ, z ^ p * (starRingEnd ℂ z) ^ q * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ) := by
  have hmp : MeasurePreserving (rotation c) (volume : Measure ℂ) volume :=
    (rotation c).measurePreserving
  have h := hmp.integral_comp (rotation c).toHomeomorph.measurableEmbedding
    (fun z : ℂ => z ^ p * (starRingEnd ℂ z) ^ q * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ))
  conv_lhs => rw [← h]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [rotation_apply, map_mul, norm_mul, Circle.norm_coe, one_mul, mul_pow]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Substitute using the available equality. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem fock_monomial_orthogonality : FockMonomialOrthogonality := by
  intro Om p q hOm
  refine ⟨fock_integrable Om hOm p q, ?_⟩
  split_ifs with hpq
  · subst hpq
    have e : ∀ z : ℂ, z ^ p * (starRingEnd ℂ z) ^ p * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ) =
        ((‖z‖ ^ (2 * p) * Real.exp (-‖z‖ ^ 2 / Om) : ℝ) : ℂ) := by
      intro z
      rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rw [pow_mul]
    simp_rw [e]
    rw [integral_complex_ofReal, fock_real_integral Om hOm (2 * p)]
    congr 1
    have h1 : ((2 * p : ℕ) : ℝ) / 2 + 1 = (p : ℝ) + 1 := by push_cast; ring
    rw [h1, Real.Gamma_nat_eq_factorial, Real.rpow_add hOm, Real.rpow_natCast, Real.rpow_one]
    ring
  ·
    have hd : ((p : ℝ) - q) ≠ 0 := by
      intro h
      apply hpq
      have : (p : ℝ) = q := by linarith
      exact_mod_cast this
    set θ : ℝ := Real.pi / ((p : ℝ) - q) with hθ
    have hrot := fock_rotate Om p q (Circle.exp θ)
    have hc : ((Circle.exp θ : Circle) : ℂ) ^ p * (starRingEnd ℂ ((Circle.exp θ : Circle) : ℂ)) ^ q
        = -1 := by
      rw [Circle.coe_exp, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
        ← Complex.exp_add]
      have : (p : ℂ) * ((θ : ℂ) * Complex.I) + (q : ℂ) * (starRingEnd ℂ) ((θ : ℂ) * Complex.I)
          = (Real.pi : ℂ) * Complex.I := by
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
        have hd' : ((p : ℂ) - q) ≠ 0 := by exact_mod_cast hd
        rw [hθ]
        push_cast
        field_simp
        ring
      rw [this, Complex.exp_pi_mul_I]
    rw [hc] at hrot
    have h2 : (2 : ℂ) * ∫ z : ℂ, z ^ p * (starRingEnd ℂ z) ^ q *
        (Real.exp (-‖z‖ ^ 2 / Om) : ℂ) = 0 := by
      linear_combination hrot
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Check the signs of the components of the expression. A detailed English derivation is pending.
-/
theorem product_of_jets : JetsProductBound := by
  intro ι _ n g₀ Th S2 hg hS2 h
  set e : ι → ℝ := fun τ => if n τ = 0 then (1 : ℝ) else min 1 ((g₀ : ℝ) / n τ) with he
  have hg0 : (0 : ℝ) < g₀ := by exact_mod_cast hg
  have hepos : ∀ τ, 0 < e τ := by
    intro τ
    simp only [he]
    split_ifs with h0
    · exact one_pos
    · have : (0 : ℝ) < n τ := by exact_mod_cast Nat.pos_of_ne_zero h0
      exact lt_min one_pos (div_pos hg0 this)
  have hP : 0 < ∏ τ, (1 + e τ) ^ (n τ + g₀) :=
    Finset.prod_pos (fun τ _ => pow_pos (by linarith [hepos τ]) _)
  have h' : Th * (∏ τ, (1 + e τ) ^ (n τ + g₀))⁻¹ ≤ S2 * ∏ τ, ((e τ) ^ g₀)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact h
  have h1 : Th ≤ S2 * (∏ τ, ((e τ) ^ g₀)⁻¹) * ∏ τ, (1 + e τ) ^ (n τ + g₀) := by
    rwa [← div_eq_mul_inv, div_le_iff₀ hP] at h'
  refine h1.trans ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  refine mul_le_mul_of_nonneg_left ?_ hS2
  refine Finset.prod_le_prod (fun τ _ => ?_) (fun τ _ => ?_)
  · have := hepos τ
    positivity
  · exact Formalism.LogVandermondeBounds.flipTwoThree.jet_exponential_bound (n τ) g₀ hg

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem block_operator_norm_bound : BlockOperatorNormBound := by
  intro X X' V V' _ _ _ _ _ _ A φ β hβ
  have hφ : 0 ≤ ∑ x, ‖φ x‖ ^ 2 := Finset.sum_nonneg (fun x _ => by positivity)
  have h1 : ∑ x', ‖∑ x, A x' x (φ x)‖ ^ 2 ≤ (∑ x', ∑ x, ‖A x' x‖ ^ 2) * ∑ x, ‖φ x‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun x' _ => ?_)
    have h2 : ‖∑ x, A x' x (φ x)‖ ≤ ∑ x, ‖A x' x‖ * ‖φ x‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun x _ => (A x' x).le_opNorm (φ x)))
    calc ‖∑ x, A x' x (φ x)‖ ^ 2 ≤ (∑ x, ‖A x' x‖ * ‖φ x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ ≤ (∑ x, ‖A x' x‖ ^ 2) * ∑ x, ‖φ x‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  refine ⟨h1, h1.trans (mul_le_mul_of_nonneg_right ?_ hφ)⟩
  calc ∑ x', ∑ x, ‖A x' x‖ ^ 2 ≤ ∑ _x' : X', ∑ _x : X, β :=
        Finset.sum_le_sum (fun x' _ => Finset.sum_le_sum (fun x _ => hβ x' x))
    _ = (Fintype.card X' : ℝ) * Fintype.card X * β := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Formalism.HermitianLattices.TraceIntegrality
