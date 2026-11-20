import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfI
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

namespace GlobalTheory.GramChartNear

open scoped Matrix ComplexConjugate

/- English proof (translation)
Introduce `E _ _ _ r X w τ a b hrw`. Use `set L : Matrix (Fin r) (Fin r) ℂ := mat (nmat X w) τ - 1 with hLdef`. Apply the tactic sequence `have hL : ∀ i j, ‖L i j‖ ≤ ‖w‖ := fun i j => PoinPf.nmat_entry X w τ i j`. Establish `hs : ∀ c : Fin r, ‖((sgn X.p0 (c : ℕ) : ℝ) : ℂ)‖ = 1` using `fun c => by`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs, PoinPf.abs_sgn]`.

Establish `h1 : mat (nmat X w) τ = 1 + L` using `by rw [hLdef]; abel`. Establish `key : PoinPf.Gw X w τ - PoinPf.Jd X = Lᵀ * PoinPf.Jd X + PoinPf.Jd X * L.map (starRingEnd ℂ) + Lᵀ * PoinPf.Jd X * L.map (starRingEnd ℂ)`. Rewrite using `[PoinPf.Gw, h1, Matrix.transpose_add, Matrix.transpose_one, Matrix.map_add _ (map_add (starRingEnd ℂ)), Matrix.map_one _ (map_zero _) (map_one _)]`. Use `noncomm_ring`. Rewrite using `[← Matrix.sub_apply, key, Matrix.add_apply, Matrix.add_apply, PoinPf.Jd, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply]`.

Repeatedly rewrite using `[Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]`. Establish `t1 : ‖L b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ)‖ ≤ ‖w‖`. Rewrite using `[norm_mul, hs, mul_one]`. Conclude with `hL b a`. Establish `t2 : ‖((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L a b)‖ ≤ ‖w‖`.

Rewrite using `[norm_mul, hs, one_mul, Complex.norm_conj]`. Conclude with `hL a b`. Establish `t3 : ‖∑ c, L c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L c b)‖ ≤ ‖w‖`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_mul, hs, mul_one, Complex.norm_conj]`. Conclude with `mul_le_mul (hL c a) (hL c b) (norm_nonneg _) (norm_nonneg _)`. Use `_ = ‖w‖ * ((r : ℝ) * ‖w‖) := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hrw (norm_nonneg _)`. Use `_ = ‖w‖ := mul_one _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gw_sub_jd_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (w : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (a b : Fin r), (r : ℝ) * ‖w‖ ≤ 1 → ‖ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Gw X w τ a b - ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Jd X a b‖ ≤ 3 * ‖w‖ := by
  intro E _ _ _ r X w τ a b hrw
  set L : Matrix (Fin r) (Fin r) ℂ := mat (nmat X w) τ - 1 with hLdef
  have hL : ∀ i j, ‖L i j‖ ≤ ‖w‖ := fun i j => PoinPf.nmat_entry X w τ i j
  have hs : ∀ c : Fin r, ‖((sgn X.p0 (c : ℕ) : ℝ) : ℂ)‖ = 1 := fun c => by
    rw [Complex.norm_real, Real.norm_eq_abs, PoinPf.abs_sgn]
  have h1 : mat (nmat X w) τ = 1 + L := by rw [hLdef]; abel
  have key : PoinPf.Gw X w τ - PoinPf.Jd X =
      Lᵀ * PoinPf.Jd X + PoinPf.Jd X * L.map (starRingEnd ℂ) + Lᵀ * PoinPf.Jd X * L.map (starRingEnd ℂ) := by
    rw [PoinPf.Gw, h1, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.map_add _ (map_add (starRingEnd ℂ)), Matrix.map_one _ (map_zero _) (map_one _)]
    noncomm_ring
  rw [← Matrix.sub_apply, key, Matrix.add_apply, Matrix.add_apply, PoinPf.Jd, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]
  have t1 : ‖L b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ)‖ ≤ ‖w‖ := by
    rw [norm_mul, hs, mul_one]; exact hL b a
  have t2 : ‖((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L a b)‖ ≤ ‖w‖ := by
    rw [norm_mul, hs, one_mul, Complex.norm_conj]; exact hL a b
  have t3 : ‖∑ c, L c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L c b)‖ ≤ ‖w‖ := by
    calc _ ≤ ∑ c : Fin r, ‖L c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L c b)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _c : Fin r, ‖w‖ * ‖w‖ := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul, norm_mul, hs, mul_one, Complex.norm_conj]
          exact mul_le_mul (hL c a) (hL c b) (norm_nonneg _) (norm_nonneg _)
      _ = ‖w‖ * ((r : ℝ) * ‖w‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hrw (norm_nonneg _)
      _ = ‖w‖ := mul_one _
  calc _ ≤ _ := norm_add₃_le
    _ ≤ ‖w‖ + ‖w‖ + ‖w‖ := add_le_add (add_le_add t1 t2) t3
    _ = 3 * ‖w‖ := by ring

end GlobalTheory.GramChartNear
