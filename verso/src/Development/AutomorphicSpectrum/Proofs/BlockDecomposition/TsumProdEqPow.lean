import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailExtra

noncomputable section

open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LatticeSum

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Yvb3.main g n`.
-/
theorem tsum_prod_eq_pow (g : ℤ → ℝ≥0∞) (n : ℕ) :
    ∑' m : Fin n → ℤ, ∏ i, g (m i) = (∑' k, g k) ^ n :=
  _root_.UpperTheory.Reformulated.B.Yvb3.main g n

def wt (k : ℤ) : ℝ := ((1 + |(k : ℝ)|) ^ 2)⁻¹

/- English proof (translation)
Unfold `wt`. Check the signs of the components of the expression.
-/
theorem wt_nonneg (k : ℤ) : 0 ≤ wt k := by
  unfold wt; positivity

/- English proof (translation)
Establish `h : Summable fun k : ℕ => ((k : ℝ) ^ 2)⁻¹`. Simplify `(Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)` using `[one_div]`. Establish `h1` using `(summable_nat_add_iff 1).2 h`. Simplify using `using h1`.
-/
theorem summable_nat_wt : Summable fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹ := by
  have h : Summable fun k : ℕ => ((k : ℝ) ^ 2)⁻¹ := by
    simpa [one_div] using (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have h1 := (summable_nat_add_iff 1).2 h
  simpa using h1

/- English proof (translation)
Apply `Summable.of_nat_of_neg` to reduce the goal to its premises. Use `summable_nat_wt.congr fun k => ?_` and prove the remaining obligations. Simplify using `[wt, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k), add_comm]`. Use `summable_nat_wt.congr fun k => ?_` and prove the remaining obligations. Simplify using `[wt, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k), add_comm]`.
-/
theorem summable_wt : Summable wt := by
  apply Summable.of_nat_of_neg
  · refine summable_nat_wt.congr fun k => ?_
    simp [wt, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k), add_comm]
  · refine summable_nat_wt.congr fun k => ?_
    simp [wt, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k), add_comm]

/- English proof (translation)
Use `set N : ℝ := 1 + ‖fun i => (m i : ℝ)‖ with hN`. Establish `hN1 : 1 ≤ N`. Use `norm_nonneg (fun i => (m i : ℝ))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN0 : 0 < N` using `by linarith`.

Establish `hle : ∏ i, (1 + |(m i : ℝ)|) ^ 2 ≤ N ^ M`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `i _`. Check the signs of the components of the expression.

Introduce `i _`. Establish `h1 : |(m i : ℝ)| ≤ ‖fun i => (m i : ℝ)‖`. Simplify `norm_le_pi_norm (fun i => (m i : ℝ)) i` using `[Real.norm_eq_abs]`. Establish `h2 : 1 + |(m i : ℝ)| ≤ N` using `by rw [hN]; linarith`. Conclude with `pow_le_pow_left₀ (by positivity) h2 2`.

Use `_ = N ^ (2 * n) := by simp [Finset.prod_const, pow_mul]`. Use `_ ≤ N ^ M := pow_le_pow_right₀ hN1 h`. Establish `hpos : 0 < ∏ i, (1 + |(m i : ℝ)|) ^ 2` using `Finset.prod_pos fun i _ => by positivity`. Establish `hw : ∏ i, wt (m i) = (∏ i, (1 + |(m i : ℝ)|) ^ 2)⁻¹`. Simplify using `only [wt, Finset.prod_inv_distrib]`.

Rewrite using `[hw, zpow_neg, zpow_natCast]`. Conclude with `inv_anti₀ hpos hle`.
-/
theorem pointwise_le (n M : ℕ) (h : 2 * n ≤ M) (m : Fin n → ℤ) :
    (1 + ‖fun i => (m i : ℝ)‖) ^ (-(M : ℤ)) ≤ ∏ i, wt (m i) := by
  set N : ℝ := 1 + ‖fun i => (m i : ℝ)‖ with hN
  have hN1 : 1 ≤ N := by
    have := norm_nonneg (fun i => (m i : ℝ))
    linarith
  have hN0 : 0 < N := by linarith
  have hle : ∏ i, (1 + |(m i : ℝ)|) ^ 2 ≤ N ^ M := by
    calc ∏ i, (1 + |(m i : ℝ)|) ^ 2 ≤ ∏ _i : Fin n, N ^ 2 := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i _
            have h1 : |(m i : ℝ)| ≤ ‖fun i => (m i : ℝ)‖ := by
              simpa [Real.norm_eq_abs] using norm_le_pi_norm (fun i => (m i : ℝ)) i
            have h2 : 1 + |(m i : ℝ)| ≤ N := by rw [hN]; linarith
            exact pow_le_pow_left₀ (by positivity) h2 2
      _ = N ^ (2 * n) := by simp [Finset.prod_const, pow_mul]
      _ ≤ N ^ M := pow_le_pow_right₀ hN1 h
  have hpos : 0 < ∏ i, (1 + |(m i : ℝ)|) ^ 2 := Finset.prod_pos fun i _ => by positivity
  have hw : ∏ i, wt (m i) = (∏ i, (1 + |(m i : ℝ)|) ^ 2)⁻¹ := by
    simp only [wt, Finset.prod_inv_distrib]
  rw [hw, zpow_neg, zpow_natCast]
  exact inv_anti₀ hpos hle

/- English proof (translation)
Introduce `n M h`. Establish `hS : ∑' k, ENNReal.ofReal (wt k) ≠ ⊤` using `summable_wt.tsum_ofReal_ne_top`. Establish `hle : ∑' m : Fin n → ℤ, ENNReal.ofReal ((1 + ‖fun i => (m i : ℝ)‖) ^ (-(M : ℤ))) ≤ ∑' m : Fin n → ℤ, ∏ i, ENNReal.ofReal (wt (m i))`. Use `ENNReal.tsum_le_tsum fun m => ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_prod_of_nonneg fun i _ => wt_nonneg (m i)]`.

Conclude with `ENNReal.ofReal_le_ofReal (pointwise_le n M h m)`. Conclude with `ne_top_of_le_ne_top (ENNReal.pow_ne_top hS) (hle.trans_eq (tsum_prod_eq_pow (fun k => ENNReal.ofReal (wt k)) n))`.
-/
theorem latSum : PositivityTheory.Rg.BcB.E1.LatSum := by
  intro n M h
  have hS : ∑' k, ENNReal.ofReal (wt k) ≠ ⊤ := summable_wt.tsum_ofReal_ne_top
  have hle : ∑' m : Fin n → ℤ, ENNReal.ofReal ((1 + ‖fun i => (m i : ℝ)‖) ^ (-(M : ℤ))) ≤
      ∑' m : Fin n → ℤ, ∏ i, ENNReal.ofReal (wt (m i)) := by
    refine ENNReal.tsum_le_tsum fun m => ?_
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => wt_nonneg (m i)]
    exact ENNReal.ofReal_le_ofReal (pointwise_le n M h m)
  exact ne_top_of_le_ne_top (ENNReal.pow_ne_top hS)
    (hle.trans_eq (tsum_prod_eq_pow (fun k => ENNReal.ofReal (wt k)) n))

end GlobalTheory.CompanionTheory.LatticeSum

end
