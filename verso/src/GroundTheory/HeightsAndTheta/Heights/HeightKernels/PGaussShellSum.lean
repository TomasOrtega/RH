import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

noncomputable section

namespace PGaussShellSum

/- English proof (translation)
Establish `h2 : (2 : ℝ) ≤ Real.exp 1`. Use `Real.add_one_le_exp (1 : ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpos : 0 < Real.exp 1` using `Real.exp_pos 1`. Establish `he : Real.exp (-1) ≤ 1 / 2`.

Rewrite using `[Real.exp_neg, inv_eq_one_div]`. Conclude with `one_div_le_one_div_of_le (by norm_num) h2`. Establish `hlt : 0 < 1 - Real.exp (-1)` using `by linarith`. Rewrite using `[inv_le_comm₀ hlt (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem inv_one_sub_exp_neg_one_le_two : (1 - Real.exp (-1))⁻¹ ≤ 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have he : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hlt : 0 < 1 - Real.exp (-1) := by linarith
  rw [inv_le_comm₀ hlt (by norm_num)]
  linarith

/- English proof (translation)
Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_neg_nat (m : ℕ) : Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end PGaussShellSum

open PGaussShellSum in

/- English proof (translation)
Introduce `n hn Λ δ hδ hmin`. Use `set K : ℝ := gaussShellConst n * (1 + 1 / δ) ^ n with hK`. Set `f : Λ → ℝ` to `fun μ => Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)`. Establish `hf : 0 ≤ f` using `fun μ => (Real.exp_pos _).le`. Establish `hK0 : 0 ≤ K`.

Establish `hc : 0 ≤ gaussShellConst n` using `by unfold gaussShellConst; positivity`. Establish `: 0 ≤ 1 + 1 / δ` using `by positivity`. Check the signs of the components of the expression. Establish `hr0 : 0 ≤ Real.exp (-1)` using `(Real.exp_pos _).le`. Establish `hr1 : Real.exp (-1) < 1`.

Conclude with `Real.exp_lt_one_iff.2 (by norm_num)`. Establish `hgeo : Summable fun j : ℕ => K * Real.exp (-1) ^ j` using `(summable_geometric_of_lt_one hr0 hr1).mul_left K`. Establish `hbound : ∀ u : Finset Λ, ∑ μ ∈ u, f μ ≤ 2 * gaussShellConst n * (1 + 1 / δ) ^ n`. Introduce `u`. Set `fl : Λ → ℕ` to `fun μ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊`.

Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := fl) (t := u.image fl) (fun μ hμ => Finset.mem_image_of_mem fl hμ) f]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← exp_neg_nat]`. Conclude with `hS n hn Λ δ hδ hmin u j`.

Use `_ ≤ ∑' j : ℕ, K * Real.exp (-1) ^ j := hgeo.sum_le_tsum _ (fun j _ => by positivity)`. Use `_ = K * (1 - Real.exp (-1))⁻¹ := by`. Rewrite using `[tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]`. Use `_ ≤ K * 2 := mul_le_mul_of_nonneg_left inv_one_sub_exp_neg_one_le_two hK0`. Use `_ = 2 * gaussShellConst n * (1 + 1 / δ) ^ n := by rw [hK]; ring`.

Conclude with `⟨summable_of_sum_le hf hbound, Real.tsum_le_of_sum_le hf hbound⟩`.
-/
theorem GaussShellSum.proof (hS : GaussShell.Statement) : GaussShellSum.Statement := by
  intro n hn Λ δ hδ hmin
  set K : ℝ := gaussShellConst n * (1 + 1 / δ) ^ n with hK
  let f : Λ → ℝ := fun μ => Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)
  have hf : 0 ≤ f := fun μ => (Real.exp_pos _).le
  have hK0 : 0 ≤ K := by
    have hc : 0 ≤ gaussShellConst n := by unfold gaussShellConst; positivity
    have : 0 ≤ 1 + 1 / δ := by positivity
    positivity
  have hr0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hr1 : Real.exp (-1) < 1 := by
    exact Real.exp_lt_one_iff.2 (by norm_num)
  have hgeo : Summable fun j : ℕ => K * Real.exp (-1) ^ j :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left K
  have hbound : ∀ u : Finset Λ, ∑ μ ∈ u, f μ ≤ 2 * gaussShellConst n * (1 + 1 / δ) ^ n := by
    intro u
    let fl : Λ → ℕ := fun μ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊
    rw [← Finset.sum_fiberwise_of_maps_to (g := fl) (t := u.image fl)
      (fun μ hμ => Finset.mem_image_of_mem fl hμ) f]
    calc ∑ j ∈ u.image fl, ∑ μ ∈ u with fl μ = j, f μ
        ≤ ∑ j ∈ u.image fl, K * Real.exp (-1) ^ j := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← exp_neg_nat]
          exact hS n hn Λ δ hδ hmin u j
      _ ≤ ∑' j : ℕ, K * Real.exp (-1) ^ j :=
          hgeo.sum_le_tsum _ (fun j _ => by positivity)
      _ = K * (1 - Real.exp (-1))⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      _ ≤ K * 2 := mul_le_mul_of_nonneg_left inv_one_sub_exp_neg_one_le_two hK0
      _ = 2 * gaussShellConst n * (1 + 1 / δ) ^ n := by rw [hK]; ring
  exact ⟨summable_of_sum_le hf hbound, Real.tsum_le_of_sum_le hf hbound⟩

end

end GroundTheory.Heights₂.Heights
