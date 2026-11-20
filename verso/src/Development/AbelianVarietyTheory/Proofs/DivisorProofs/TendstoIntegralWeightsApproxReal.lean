import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial GlobalTheory.FlagPoly Formalism.DegreeFormula Filter Topology

namespace GlobalTheory.WeightApprox

/- English proof (translation)
Unfold `linRoot`. Rewrite using `[mul_neg, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[C_mul, mul_assoc]`.
-/
theorem linRoot_smul {ι : Type} [Fintype ι] {N : ℕ} (t : ℝ) (w : ι → Fin N → ℝ) :
    linRoot (fun τ i => t * w τ i) = C t * linRoot w := by
  unfold linRoot
  rw [mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [C_mul, mul_assoc]

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => intro Q`. Simplify using `only [pow_zero, one_mul]`. Conclude with `continuous_const`. Consider the case `succ d ih`.

Introduce `Q`. Establish `key : ∀ lam : ι → Fin N → ℝ, Φ (linRoot lam ^ (d + 1) * Q) = -∑ x : ι × Fin N, lam x.1 x.2 * Φ (linRoot lam ^ d * (X x * Q))`. Introduce `lam`. Establish `hL : ∀ R : Pol ι N, linRoot lam * R = -∑ x : ι × Fin N, C (lam x.1 x.2) * (X x * R)`. Introduce `R`.

Unfold `linRoot`. Rewrite using `[neg_mul, Finset.sum_mul]`. Simplify using `only [mul_assoc]`. Establish `: linRoot lam ^ (d + 1) * Q = -∑ x : ι × Fin N, C (lam x.1 x.2) * (linRoot lam ^ d * (X x * Q))`. Rewrite using `[pow_succ', mul_assoc, hL]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, map_neg, map_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[C_mul', map_smul, smul_eq_mul]`. Repeatedly rewrite using `[key]`. Use `Continuous.neg (continuous_finset_sum _ fun x _ => ?_)` and prove the remaining obligations. Establish `hc : Continuous fun lam : ι → Fin N → ℝ => lam x.1 x.2` using `by fun_prop`.

Conclude with `hc.mul (ih (X x * Q))`.
-/
theorem continuous_comp_of_filtered_continuity {ι : Type} [Fintype ι] {N : ℕ} (Φ : Pol ι N →ₗ[ℝ] ℝ) (d : ℕ) :
    ∀ Q : Pol ι N, Continuous (fun lam : ι → Fin N → ℝ => Φ (linRoot lam ^ d * Q)) := by
  induction d with
  | zero => intro Q; simp only [pow_zero, one_mul]; exact continuous_const
  | succ d ih =>
    intro Q
    have key : ∀ lam : ι → Fin N → ℝ, Φ (linRoot lam ^ (d + 1) * Q) =
        -∑ x : ι × Fin N, lam x.1 x.2 * Φ (linRoot lam ^ d * (X x * Q)) := by
      intro lam
      have hL : ∀ R : Pol ι N, linRoot lam * R = -∑ x : ι × Fin N, C (lam x.1 x.2) * (X x * R) := by
        intro R
        unfold linRoot
        rw [neg_mul, Finset.sum_mul]
        simp only [mul_assoc]
      have : linRoot lam ^ (d + 1) * Q =
          -∑ x : ι × Fin N, C (lam x.1 x.2) * (linRoot lam ^ d * (X x * Q)) := by
        rw [pow_succ', mul_assoc, hL]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      rw [this, map_neg, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [C_mul', map_smul, smul_eq_mul]
    simp_rw [key]
    refine Continuous.neg (continuous_finset_sum _ fun x _ => ?_)
    have hc : Continuous fun lam : ι → Fin N → ℝ => lam x.1 x.2 := by fun_prop
    exact hc.mul (ih (X x * Q))

/- English proof (translation)
Introduce `ι _ N Φ d lam`. Use `⟨fun m τ i => ⌊((m : ℝ) + 1) * lam τ i⌋, fun m => 1 / ((m : ℝ) + 1) ^ d, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `m`. Check the signs of the components of the expression. Introduce `m τ a b h`.

Conclude with `Int.floor_mono (mul_le_mul_of_nonneg_left h (by positivity))`. Establish `hcont : Continuous (fun w : ι → Fin N → ℝ => Φ (linRoot w ^ d))`. Simplify using `using continuous_comp_of_filtered_continuity Φ d 1`. Use `set v : ℕ → ι → Fin N → ℝ := fun m τ i => 1 / ((m : ℝ) + 1) * (⌊((m : ℝ) + 1) * lam τ i⌋ : ℝ) with hv`. Establish `heq : ∀ m : ℕ, 1 / ((m : ℝ) + 1) ^ d * Φ (linRoot (fun τ i => ((⌊((m : ℝ) + 1) * lam τ i⌋ : ℤ) : ℝ)) ^ d) = Φ (linRoot (v m) ^ d)`.

Introduce `m`. Rewrite using `[hv]`. Simplify using `only`. Rewrite using `[linRoot_smul, mul_pow, ← C_pow, C_mul', map_smul, smul_eq_mul, one_div_pow]`. Repeatedly rewrite using `[heq]`.

Establish `hlim : Tendsto v atTop (𝓝 lam)`. Rewrite using `[tendsto_pi_nhds]`. Introduce `τ`. Rewrite using `[tendsto_pi_nhds]`. Introduce `i`.

Establish `h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)` using `tendsto_one_div_add_atTop_nhds_zero_nat`. Establish `hlow : Tendsto (fun m : ℕ => lam τ i - 1 / ((m : ℝ) + 1)) atTop (𝓝 (lam τ i))`. Establish `h2` using `(tendsto_const_nhds : Tendsto (fun _ : ℕ => lam τ i) atTop (𝓝 (lam τ i))).sub h0`. Simplify using `using h2`. Use `tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds ?_ ?_` and prove the remaining obligations.

Introduce `m`. Establish `hp : (0 : ℝ) < (m : ℝ) + 1` using `by positivity`. Establish `h1` using `Int.sub_one_lt_floor (((m : ℝ) + 1) * lam τ i)`. Use `show lam τ i - 1 / ((m : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) * (⌊((m : ℝ) + 1) * lam τ i⌋ : ℝ)`. Rewrite using `[one_div_mul_eq_div, le_div_iff₀ hp, sub_mul, one_div_mul_cancel hp.ne']`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `m`. Establish `hp : (0 : ℝ) < (m : ℝ) + 1` using `by positivity`. Establish `h1` using `Int.floor_le (((m : ℝ) + 1) * lam τ i)`. Use `show 1 / ((m : ℝ) + 1) * (⌊((m : ℝ) + 1) * lam τ i⌋ : ℝ) ≤ lam τ i`.

Rewrite using `[one_div, inv_mul_eq_div, div_le_iff₀ hp]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(hcont.tendsto lam).comp hlim`.
-/
theorem approx : ∀ (ι : Type) [Fintype ι] (N : ℕ) (Φ : Pol ι N →ₗ[ℝ] ℝ) (d : ℕ) (lam : ι → Fin N → ℝ), ∃ (u : ℕ → ι → Fin N → ℤ) (c : ℕ → ℝ), (∀ m, 0 < c m) ∧ (∀ m τ (a b : Fin N), lam τ a ≤ lam τ b → u m τ a ≤ u m τ b) ∧ Tendsto (fun m => c m * Φ (linRoot (fun τ i => (u m τ i : ℝ)) ^ d)) atTop (𝓝 (Φ (linRoot lam ^ d))) := by
  intro ι _ N Φ d lam
  refine ⟨fun m τ i => ⌊((m : ℝ) + 1) * lam τ i⌋, fun m => 1 / ((m : ℝ) + 1) ^ d, ?_, ?_, ?_⟩
  · intro m; positivity
  · intro m τ a b h
    exact Int.floor_mono (mul_le_mul_of_nonneg_left h (by positivity))
  · have hcont : Continuous (fun w : ι → Fin N → ℝ => Φ (linRoot w ^ d)) := by
      simpa using continuous_comp_of_filtered_continuity Φ d 1
    set v : ℕ → ι → Fin N → ℝ := fun m τ i => 1 / ((m : ℝ) + 1) * (⌊((m : ℝ) + 1) * lam τ i⌋ : ℝ)
      with hv
    have heq : ∀ m : ℕ, 1 / ((m : ℝ) + 1) ^ d *
        Φ (linRoot (fun τ i => ((⌊((m : ℝ) + 1) * lam τ i⌋ : ℤ) : ℝ)) ^ d) = Φ (linRoot (v m) ^ d) := by
      intro m
      rw [hv]
      simp only
      rw [linRoot_smul, mul_pow, ← C_pow, C_mul', map_smul, smul_eq_mul, one_div_pow]
    simp_rw [heq]
    have hlim : Tendsto v atTop (𝓝 lam) := by
      rw [tendsto_pi_nhds]; intro τ
      rw [tendsto_pi_nhds]; intro i
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hlow : Tendsto (fun m : ℕ => lam τ i - 1 / ((m : ℝ) + 1)) atTop (𝓝 (lam τ i)) := by
        have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => lam τ i) atTop (𝓝 (lam τ i))).sub h0
        simpa using h2
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds ?_ ?_
      · intro m
        have hp : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        have h1 := Int.sub_one_lt_floor (((m : ℝ) + 1) * lam τ i)
        show lam τ i - 1 / ((m : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) * (⌊((m : ℝ) + 1) * lam τ i⌋ : ℝ)
        rw [one_div_mul_eq_div, le_div_iff₀ hp, sub_mul, one_div_mul_cancel hp.ne']
        linarith
      · intro m
        have hp : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        have h1 := Int.floor_le (((m : ℝ) + 1) * lam τ i)
        show 1 / ((m : ℝ) + 1) * (⌊((m : ℝ) + 1) * lam τ i⌋ : ℝ) ≤ lam τ i
        rw [one_div, inv_mul_eq_div, div_le_iff₀ hp]
        linarith
    exact (hcont.tendsto lam).comp hlim

end GlobalTheory.WeightApprox
