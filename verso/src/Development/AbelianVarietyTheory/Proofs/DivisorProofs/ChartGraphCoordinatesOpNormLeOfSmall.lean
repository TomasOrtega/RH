import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBottomLeftBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFirstColumnsEqGraphTimesTopBlock
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

open Matrix

/- English proof (translation)
Establish `hi : ∀ i, ‖(M *ᵥ w) i‖ ≤ c * ∑ j, ‖w j‖`. Introduce `i`. Simplify using `only [Matrix.mulVec, dotProduct]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_right (h i j) (norm_nonneg _)`. Use `_ = c * ∑ j, ‖w j‖ := by rw [Finset.mul_sum]`. Establish `hs : (∑ j, ‖w j‖) ^ 2 ≤ n * ∑ j, ‖w j‖ ^ 2`. Simplify using `using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖w j‖)`. Establish `hi2 : ∀ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ c ^ 2 * (n * ∑ j, ‖w j‖ ^ 2)` using `fun i => by`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_norm_mulVec_sq_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (c : ℝ)
    (h : ∀ i j, ‖M i j‖ ≤ c) (w : Fin n → ℂ) :
    ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ ((m : ℝ) * n * c ^ 2) * ∑ j, ‖w j‖ ^ 2 := by
  have hi : ∀ i, ‖(M *ᵥ w) i‖ ≤ c * ∑ j, ‖w j‖ := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    calc ‖∑ j, M i j * w j‖ ≤ ∑ j, ‖M i j * w j‖ := norm_sum_le _ _
      _ ≤ ∑ j, c * ‖w j‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h i j) (norm_nonneg _)
      _ = c * ∑ j, ‖w j‖ := by rw [Finset.mul_sum]
  have hs : (∑ j, ‖w j‖) ^ 2 ≤ n * ∑ j, ‖w j‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖w j‖)
  have hi2 : ∀ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ c ^ 2 * (n * ∑ j, ‖w j‖ ^ 2) := fun i => by
    calc ‖(M *ᵥ w) i‖ ^ 2 ≤ (c * ∑ j, ‖w j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hi i) 2
      _ = c ^ 2 * (∑ j, ‖w j‖) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (sq_nonneg c)
  calc ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ ∑ _i : Fin m, c ^ 2 * (n * ∑ j, ‖w j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => hi2 i
    _ = _ := by simp [Finset.sum_const]; ring

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq]`.
-/
theorem sqrt_sum_norm_sq_eq {n : ℕ} (x : Fin n → ℂ) :
    Real.sqrt (∑ i, ‖x i‖ ^ 2) = ‖WithLp.toLp 2 x‖ := by
  rw [EuclideanSpace.norm_eq]

/- English proof (translation)
Rewrite using `[← sqrt_sum_norm_sq_eq, ← sqrt_sum_norm_sq_eq]`. Establish `hmn : (m : ℝ) * n * c ^ 2 ≤ ((r : ℝ) * c) ^ 2`. Establish `h1 : (m : ℝ) ≤ r` using `by exact_mod_cast hm`. Establish `h2 : (n : ℝ) ≤ r` using `by exact_mod_cast hn`. Establish `: (m : ℝ) * n ≤ (r : ℝ) * r` using `mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)`.

Use polynomial arithmetic with `[sq_nonneg c]`. Establish `hS` using `sum_norm_mulVec_sq_le M c h w`. Establish `hB : 0 ≤ ∑ j, ‖w j‖ ^ 2` using `Finset.sum_nonneg fun _ _ => sq_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) hc)]`.
-/
theorem norm_toLp_mulVec_le {m n r : ℕ} (hm : m ≤ r) (hn : n ≤ r) (M : Matrix (Fin m) (Fin n) ℂ)
    (c : ℝ) (hc : 0 ≤ c) (h : ∀ i j, ‖M i j‖ ≤ c) (w : Fin n → ℂ) :
    ‖WithLp.toLp 2 (M *ᵥ w)‖ ≤ (r * c) * ‖WithLp.toLp 2 w‖ := by
  rw [← sqrt_sum_norm_sq_eq, ← sqrt_sum_norm_sq_eq]
  have hmn : (m : ℝ) * n * c ^ 2 ≤ ((r : ℝ) * c) ^ 2 := by
    have h1 : (m : ℝ) ≤ r := by exact_mod_cast hm
    have h2 : (n : ℝ) ≤ r := by exact_mod_cast hn
    have : (m : ℝ) * n ≤ (r : ℝ) * r :=
      mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith [sq_nonneg c]
  have hS := sum_norm_mulVec_sq_le M c h w
  have hB : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc Real.sqrt (∑ i, ‖(M *ᵥ w) i‖ ^ 2) ≤ Real.sqrt (((r : ℝ) * c) ^ 2 * ∑ j, ‖w j‖ ^ 2) :=
        Real.sqrt_le_sqrt (hS.trans (mul_le_mul_of_nonneg_right hmn hB))
    _ = (r * c) * Real.sqrt (∑ j, ‖w j‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) hc)]

end GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
The claim follows from `PiLp.norm_apply_le z k`.
-/
theorem norm_coord_le (X : Data E r) (z : V (nd X)) (k : Fin (nd X)) : ‖z k‖ ≤ ‖z‖ :=
  PiLp.norm_apply_le z k

/- English proof (translation)
Simplify using `only [chartMatrixTopBlock, Matrix.sub_apply, Matrix.submatrix_apply, mat, Matrix.of_apply, nmat, Matrix.one_apply]`. Use `split_ifs`. Apply the tactic sequence `all_goals first`. Consider the case `(rw [sub_zero]; exact norm_coord_le X z _)`. Consider the case `(rw [sub_self, norm_zero]; exact norm_nonneg _)`.

Consider the case `(exfalso; simp only [Fin.lt_def, Fin.ext_iff, Fin.coe_castLE] at *; omega)`.
-/
theorem norm_chartMatrixTopBlock_sub_one_le (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (i j : Fin X.p0) :
    ‖(chartMatrixTopBlock X z τ - 1) i j‖ ≤ ‖z‖ := by
  simp only [chartMatrixTopBlock, Matrix.sub_apply, Matrix.submatrix_apply, mat, Matrix.of_apply, nmat,
    Matrix.one_apply]
  split_ifs
  all_goals first
    | (rw [sub_zero]; exact norm_coord_le X z _)
    | (rw [sub_self, norm_zero]; exact norm_nonneg _)
    | (exfalso; simp only [Fin.lt_def, Fin.ext_iff, Fin.coe_castLE] at *; omega)

/- English proof (translation)
Simplify using `only [chartBottomLeftBlock, Matrix.submatrix_apply, mat, Matrix.of_apply, nmat]`. Use `split_ifs with h1 h2`. Conclude with `norm_coord_le X z _`. Conclude with `absurd h2 (by intro h; have := congrArg Fin.val h; simp at this; omega)`. Conclude with `absurd (show Fin.castLE X.p0_le j < ⟨X.p0 + i, by have := i.isLt; have := X.p0_le; omega⟩ from by rw [Fin.lt_def]; simp; omega) h1`.
-/
theorem norm_chartBottomLeftBlock_le (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (i : Fin (r - X.p0)) (j : Fin X.p0) :
    ‖chartBottomLeftBlock X z τ i j‖ ≤ ‖z‖ := by
  simp only [chartBottomLeftBlock, Matrix.submatrix_apply, mat, Matrix.of_apply, nmat]
  split_ifs with h1 h2
  · exact norm_coord_le X z _
  · exact absurd h2 (by intro h; have := congrArg Fin.val h; simp at this; omega)
  · exact absurd (show Fin.castLE X.p0_le j < ⟨X.p0 + i, by have := i.isLt; have := X.p0_le; omega⟩ from
      by rw [Fin.lt_def]; simp; omega) h1

end GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

open Matrix

/- English proof (translation)
Introduce `E _ _ _ r X z hz`. Establish `hε : 0 ≤ ‖z‖` using `norm_nonneg z`. Establish `hrε : (r : ℝ) * ‖z‖ ≤ 1 / 100`. Break down `Nat.eq_zero_or_pos r with h | h` into its components or cases. Simplify using `[h]`.

Establish `h1 : (1 : ℝ) ≤ r` using `by exact_mod_cast h`. Use the polynomial consequences of the given equalities and inequalities. Apply `Real.iSup_le _ (by norm_num)` to reduce the goal to its premises. Introduce `τ`. Apply `Real.sSup_le _ (by norm_num)` to reduce the goal to its premises.

Introduce and unpack `t ⟨v, hv, rfl⟩`. Establish `hunit : IsUnit (chartMatrixTopBlock X z τ).det` using `by rw [chartMatrixTopBlock_det_eq_one]; exact isUnit_one`. Establish `hAv : Matrix.of (graphCoord X z τ) *ᵥ v = chartBottomLeftBlock X z τ *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)`. Express the relevant statement in the definitionally equal form `(chartBottomLeftBlock X z τ * (chartMatrixTopBlock X z τ)⁻¹) *ᵥ v = _`. Conclude with `(Matrix.mulVec_mulVec _ _ _).symm`.

Establish `hvw : v = (chartMatrixTopBlock X z τ)⁻¹ *ᵥ v + (chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Establish `h1` using `norm_toLp_mulVec_le (Nat.sub_le r X.p0) X.p0_le (chartBottomLeftBlock X z τ) ‖z‖ hε (norm_chartBottomLeftBlock_le X z τ) ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)`. Establish `h2` using `norm_toLp_mulVec_le X.p0_le X.p0_le (chartMatrixTopBlock X z τ - 1) ‖z‖ hε (norm_chartMatrixTopBlock_sub_one_le X z τ) ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)`.

Establish `h3 : ‖WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)‖ ≤ ‖WithLp.toLp 2 v‖ + ‖WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v))‖`. Establish `hv' : WithLp.toLp 2 v = WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) + WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v))`. Rewrite using `[← WithLp.toLp_add, ← hvw]`. Establish `: WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) = WithLp.toLp 2 v - WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v))`. Rewrite using `[hv', add_sub_cancel_right]`.

Rewrite using `[this]`. Conclude with `norm_sub_le _ _`. Establish `hvpos : 0 < ‖WithLp.toLp 2 v‖` using `norm_pos_iff.mpr fun h => hv (by simpa using congrArg WithLp.ofLp h)`. Rewrite using `[sqrt_sum_norm_sq_eq, sqrt_sum_norm_sq_eq, hAv, div_le_iff₀ hvpos]`. Establish `hb` using `norm_nonneg (WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v))`.

Establish `h4` using `mul_le_mul_of_nonneg_right hrε hb`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem zN_graphCoord_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (z : V (nd X)), (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 → X.zN (graphCoord X z) ≤ 1 / 50 := by
  intro E _ _ _ r X z hz
  have hε : 0 ≤ ‖z‖ := norm_nonneg z
  have hrε : (r : ℝ) * ‖z‖ ≤ 1 / 100 := by
    rcases Nat.eq_zero_or_pos r with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ r := by exact_mod_cast h
      nlinarith
  apply Real.iSup_le _ (by norm_num)
  intro τ
  apply Real.sSup_le _ (by norm_num)
  rintro t ⟨v, hv, rfl⟩
  have hunit : IsUnit (chartMatrixTopBlock X z τ).det := by rw [chartMatrixTopBlock_det_eq_one]; exact isUnit_one
  have hAv : Matrix.of (graphCoord X z τ) *ᵥ v = chartBottomLeftBlock X z τ *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) := by
    change (chartBottomLeftBlock X z τ * (chartMatrixTopBlock X z τ)⁻¹) *ᵥ v = _
    exact (Matrix.mulVec_mulVec _ _ _).symm
  have hvw : v = (chartMatrixTopBlock X z τ)⁻¹ *ᵥ v + (chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
    abel
  have h1 := norm_toLp_mulVec_le (Nat.sub_le r X.p0) X.p0_le (chartBottomLeftBlock X z τ) ‖z‖ hε
    (norm_chartBottomLeftBlock_le X z τ) ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)
  have h2 := norm_toLp_mulVec_le X.p0_le X.p0_le (chartMatrixTopBlock X z τ - 1) ‖z‖ hε
    (norm_chartMatrixTopBlock_sub_one_le X z τ) ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)
  have h3 : ‖WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)‖ ≤ ‖WithLp.toLp 2 v‖ +
      ‖WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v))‖ := by
    have hv' : WithLp.toLp 2 v = WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) +
        WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)) := by
      rw [← WithLp.toLp_add, ← hvw]
    have : WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) = WithLp.toLp 2 v -
        WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)) := by
      rw [hv', add_sub_cancel_right]
    rw [this]
    exact norm_sub_le _ _
  have hvpos : 0 < ‖WithLp.toLp 2 v‖ :=
    norm_pos_iff.mpr fun h => hv (by simpa using congrArg WithLp.ofLp h)
  rw [sqrt_sum_norm_sq_eq, sqrt_sum_norm_sq_eq, hAv, div_le_iff₀ hvpos]
  have hb := norm_nonneg (WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v))
  have h4 := mul_le_mul_of_nonneg_right hrε hb
  linarith

end GlobalTheory.ChartGraph
