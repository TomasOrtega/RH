import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.PaUContinuous
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaSA

namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem Hf_add_left (x y z : EuclideanSpace ℂ ι) : Hf (x + y) z = Hf x z + Hf y z := by
  simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem Hf_add_right (x y z : EuclideanSpace ℂ ι) : Hf z (x + y) = Hf z x + Hf z y := by
  simp only [Hf, PiLp.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem Hf_neg_left (x z : EuclideanSpace ℂ ι) : Hf (-x) z = -Hf x z := by
  simp only [Hf, PiLp.neg_apply, neg_mul, Finset.sum_neg_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem Hf_conj (x y : EuclideanSpace ℂ ι) : (starRingEnd ℂ) (Hf x y) = Hf y x := by
  simp only [Hf, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Both sides reduce to the same expression.
-/
theorem Hf_self (x : EuclideanSpace ℂ ι) : Hf x x = ((‖x‖ : ℝ) : ℂ) ^ 2 := by
  rw [← Complex.ofReal_pow, EuclideanSpace.norm_sq_eq]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_eq_sub (z : ℂ) : (starRingEnd ℂ) z = z - 2 * (z.im : ℂ) * I := by
  apply Complex.ext <;> simp
  ring

def Coc (Y : GT ι) (q : ℕ) : Prop :=
  ∀ γ ∈ lat Y.b, ∀ γ' ∈ lat Y.b,
    Y.ka (γ + γ') = Y.ka γ * Y.ka γ' * cexp (-(Real.pi * q * (Hf γ γ').im) * I)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem ka_zero {Y : GT ι} {q : ℕ} (hC : Coc Y q) : Y.ka 0 = 1 := by
  have h := hC 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
  have hz : Hf (0 : EuclideanSpace ℂ ι) 0 = 0 := by simp [Hf]
  simp only [add_zero, hz, Complex.zero_im, mul_zero, neg_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one] at h
  have hne : Y.ka 0 ≠ 0 := by
    intro h0
    have h1 := Y.ka_abs 0 (Submodule.zero_mem _)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm)

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Take a linear combination of the given relations to obtain the conclusion.
-/
theorem paTh_add {Y : GT ι} {q : ℕ} (hC : Coc Y q) (F : EuclideanSpace ℂ ι → ℂ)
    {γ : EuclideanSpace ℂ ι} (hγ : γ ∈ lat Y.b) (v : EuclideanSpace ℂ ι) :
    paTh Y q F (v + γ) = Y.ka γ * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * paTh Y q F v := by
  simp only [paTh]
  rw [← (Equiv.addLeft (⟨γ, hγ⟩ : lat Y.b)).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun δ => ?_
  simp only [Equiv.coe_addLeft, Submodule.coe_add, paU]
  rw [hC γ hγ δ δ.2]
  have hF : v + γ - (γ + (δ : EuclideanSpace ℂ ι)) = v - δ := by abel
  rw [hF]
  have hexp : cexp (-(Real.pi * q * (Hf γ (δ : EuclideanSpace ℂ ι)).im) * I) *
      cexp (q * Real.pi * Hf (v + γ) (γ + (δ : EuclideanSpace ℂ ι)) -
        q * Real.pi * Hf (γ + (δ : EuclideanSpace ℂ ι)) (γ + (δ : EuclideanSpace ℂ ι)) / 2) =
      cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) *
        cexp (q * Real.pi * Hf v (δ : EuclideanSpace ℂ ι) -
          q * Real.pi * Hf (δ : EuclideanSpace ℂ ι) (δ : EuclideanSpace ℂ ι) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [Hf_add_left, Hf_add_right, Hf_add_right, Hf_add_left, Hf_add_right, Hf_add_right]
    have hc := conj_eq_sub (Hf γ (δ : EuclideanSpace ℂ ι))
    rw [Hf_conj] at hc
    rw [hc]
    ring
  linear_combination (Y.ka γ * Y.ka δ * F (v - δ)) * hexp

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
