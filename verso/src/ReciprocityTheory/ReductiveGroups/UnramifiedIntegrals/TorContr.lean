import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorChord

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]

/- English proof (translation)
Establish `hu : ‖uOf D‖ < 1` using `formalGroup_param_norm_lt_one W hW D hD`. Establish `hsq : ‖uOf D‖ ^ 2 ≤ ‖uOf D‖`. Establish `h0` using `norm_nonneg (uOf D)`. Use the polynomial consequences of the given equalities and inequalities. Proceed by induction on `n with`.

Consider the case `zero`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[zero_smul]`. Conclude with `(trivial : InFormalGroupPoints (Affine.Point.zero : W.toAffine.Point))`. Rewrite using `[zero_smul]`.

Establish `: uOf (0 : W.toAffine.Point) = 0` using `rfl`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Take `⟨h1, h2⟩` from `ih`.

Establish `hin : InFormalGroupPoints (n • D + D)` using `(formal_group_points_subgroup C W hW hΔ (n • D) D h1 hD).1`. Establish `hn : ‖(n : C)‖ ≤ 1` using `IsUltrametricDist.norm_natCast_le_one C n`. Establish `hnu : ‖(n : C) * uOf D‖ ≤ ‖uOf D‖`. Rewrite using `[norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) hn`.

Establish `hb : ‖uOf (n • D)‖ ≤ ‖uOf D‖`. Establish `e : uOf (n • D) = (uOf (n • D) - (n : C) * uOf D) + (n : C) * uOf D` using `by ring`. Rewrite using `[e]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h2.trans hsq) hnu)`. Establish `hadd` using `formalGroup_add_estimate W hW (n • D) D h1 hD`.

Rewrite `hadd` using `[max_eq_right hb]`. Rewrite using `[succ_nsmul]`. Use `⟨hin, ?_⟩` and prove the remaining obligations. Establish `e : uOf (n • D + D) - ((n + 1 : ℕ) : C) * uOf D = (uOf (n • D + D) - uOf (n • D) - uOf D) + (uOf (n • D) - (n : C) * uOf D)` using `by push_cast; ring`. Rewrite using `[e]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hadd h2)`.
-/
theorem formalGroup_nsmul_estimate (W : WeierstrassCurve C) (hW : IntegralModel W) (hΔ : ‖W.Δ‖ = 1)
    (D : W.toAffine.Point) (hD : InFormalGroupPoints D) (n : ℕ) :
    InFormalGroupPoints (n • D) ∧ ‖uOf (n • D) - (n : C) * uOf D‖ ≤ ‖uOf D‖ ^ 2 := by
  have hu : ‖uOf D‖ < 1 := formalGroup_param_norm_lt_one W hW D hD
  have hsq : ‖uOf D‖ ^ 2 ≤ ‖uOf D‖ := by
    have h0 := norm_nonneg (uOf D)
    nlinarith
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [zero_smul]; exact (trivial : InFormalGroupPoints (Affine.Point.zero : W.toAffine.Point))
    · rw [zero_smul]
      have : uOf (0 : W.toAffine.Point) = 0 := rfl
      rw [this]; simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hin : InFormalGroupPoints (n • D + D) := (formal_group_points_subgroup C W hW hΔ (n • D) D h1 hD).1
    have hn : ‖(n : C)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one C n
    have hnu : ‖(n : C) * uOf D‖ ≤ ‖uOf D‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hn
    have hb : ‖uOf (n • D)‖ ≤ ‖uOf D‖ := by
      have e : uOf (n • D) = (uOf (n • D) - (n : C) * uOf D) + (n : C) * uOf D := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h2.trans hsq) hnu)
    have hadd := formalGroup_add_estimate W hW (n • D) D h1 hD
    rw [max_eq_right hb] at hadd
    rw [succ_nsmul]
    refine ⟨hin, ?_⟩
    have e : uOf (n • D + D) - ((n + 1 : ℕ) : C) * uOf D
        = (uOf (n • D + D) - uOf (n • D) - uOf D) + (uOf (n • D) - (n : C) * uOf D) := by
      push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hadd h2)

/- English proof (translation)
Establish `hu : ‖uOf D‖ < 1` using `formalGroup_param_norm_lt_one W hW D hD`. Use `set c : ℝ := max ‖(M : C)‖ ‖uOf D‖ with hc`. Establish `hc0 : 0 ≤ c` using `le_max_of_le_left (norm_nonneg _)`. Establish `hc1 : c < 1` using `max_lt hM hu`. Establish `key : ∀ k : ℕ, ‖uOf (M ^ k • D)‖ ≤ c ^ k * ‖uOf D‖`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `hk : InFormalGroupPoints (M ^ k • D)` using `(formalGroup_nsmul_estimate W hW hΔ D hD (M ^ k)).1`.

Establish `hest` using `(formalGroup_nsmul_estimate W hW hΔ (M ^ k • D) hk M).2`. Establish `hle : ‖uOf (M ^ k • D)‖ ≤ ‖uOf D‖` using `ih.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hc0 hc1.le))`. Establish `hr0` using `norm_nonneg (uOf (M ^ k • D))`. Establish `e0 : M ^ (k + 1) • D = M • (M ^ k • D)`. Rewrite using `[smul_smul, pow_succ, mul_comm]`.

Establish `h1 : ‖uOf (M • (M ^ k • D))‖ ≤ c * ‖uOf (M ^ k • D)‖`. Establish `e : uOf (M • (M ^ k • D)) = (uOf (M • (M ^ k • D)) - (M : C) * uOf (M ^ k • D)) + (M : C) * uOf (M ^ k • D)` using `by ring`. Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hest.trans ?_) ?_)` and prove the remaining obligations. Rewrite using `[sq]`.

Conclude with `mul_le_mul_of_nonneg_right (hle.trans (le_max_right _ _)) hr0`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (le_max_left _ _) hr0`. Rewrite using `[e0, pow_succ, mul_comm (c ^ k) c, mul_assoc]`. Conclude with `h1.trans (mul_le_mul_of_nonneg_left ih hc0)`.

Establish `hlim : Filter.Tendsto (fun k : ℕ => c ^ k * ‖uOf D‖) Filter.atTop (nhds 0)`. Simplify using `using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const ‖uOf D‖`. Conclude with `squeeze_zero (fun _ => norm_nonneg _) key hlim`.
-/
theorem formalGroup_pow_tendsto_zero (W : WeierstrassCurve C) (hW : IntegralModel W) (hΔ : ‖W.Δ‖ = 1)
    (D : W.toAffine.Point) (hD : InFormalGroupPoints D) (M : ℕ) (hM : ‖(M : C)‖ < 1) :
    Filter.Tendsto (fun k : ℕ => ‖uOf (M ^ k • D)‖) Filter.atTop (nhds 0) := by
  have hu : ‖uOf D‖ < 1 := formalGroup_param_norm_lt_one W hW D hD
  set c : ℝ := max ‖(M : C)‖ ‖uOf D‖ with hc
  have hc0 : 0 ≤ c := le_max_of_le_left (norm_nonneg _)
  have hc1 : c < 1 := max_lt hM hu
  have key : ∀ k : ℕ, ‖uOf (M ^ k • D)‖ ≤ c ^ k * ‖uOf D‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : InFormalGroupPoints (M ^ k • D) := (formalGroup_nsmul_estimate W hW hΔ D hD (M ^ k)).1
      have hest := (formalGroup_nsmul_estimate W hW hΔ (M ^ k • D) hk M).2
      have hle : ‖uOf (M ^ k • D)‖ ≤ ‖uOf D‖ :=
        ih.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hc0 hc1.le))
      have hr0 := norm_nonneg (uOf (M ^ k • D))
      have e0 : M ^ (k + 1) • D = M • (M ^ k • D) := by
        rw [smul_smul, pow_succ, mul_comm]
      have h1 : ‖uOf (M • (M ^ k • D))‖ ≤ c * ‖uOf (M ^ k • D)‖ := by
        have e : uOf (M • (M ^ k • D)) = (uOf (M • (M ^ k • D)) - (M : C) * uOf (M ^ k • D))
            + (M : C) * uOf (M ^ k • D) := by ring
        rw [e]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hest.trans ?_) ?_)
        · rw [sq]
          exact mul_le_mul_of_nonneg_right (hle.trans (le_max_right _ _)) hr0
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hr0
      rw [e0, pow_succ, mul_comm (c ^ k) c, mul_assoc]
      exact h1.trans (mul_le_mul_of_nonneg_left ih hc0)
  have hlim : Filter.Tendsto (fun k : ℕ => c ^ k * ‖uOf D‖) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const ‖uOf D‖
  exact squeeze_zero (fun _ => norm_nonneg _) key hlim

end ReciprocityTheory.ChartRestriction.L1
