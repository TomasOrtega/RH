import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HsEighthLeOfSmall
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ProdSubLtEqFactorial
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PBridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Establish `hS : ∑ ab, ‖((s : ℂ) • y) ab‖ ^ 2 = s ^ 2 * ∑ ab, ‖y ab‖ ^ 2`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun ab _ => ?_` and prove the remaining obligations. Simplify using `[Pi.smul_apply, smul_eq_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]`. Rewrite using `[hs_pmat, hs_pmat, hS]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fdU_hs_smul {ε : Fin n → Bool} (s : ℝ) (y : PCoord ε → ℂ) :
    hs (pmat ((s : ℂ) • y)) = s ^ 2 * hs (pmat y) := by
  have hS : ∑ ab, ‖((s : ℂ) • y) ab‖ ^ 2 = s ^ 2 * ∑ ab, ‖y ab‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ab _ => ?_
    simp [Pi.smul_apply, smul_eq_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hs_pmat, hs_pmat, hS]
  ring

/- English proof (translation)
Rewrite using `[hs_pmat]`. Check the signs of the components of the expression.
-/
theorem fdU_hs_nonneg {ε : Fin n → Bool} (y : PCoord ε → ℂ) : 0 ≤ hs (pmat y) := by
  rw [hs_pmat]; positivity

/- English proof (translation)
Rewrite using `[fdU_hs_smul, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0]`.
-/
theorem fdU_sqrt_hs_smul {ε : Fin n → Bool} {s : ℝ} (hs0 : 0 ≤ s) (y : PCoord ε → ℂ) :
    Real.sqrt (hs (pmat ((s : ℂ) • y))) = s * Real.sqrt (hs (pmat y)) := by
  rw [fdU_hs_smul, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0]

/- English proof (translation)
Unfold `Qf`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun ab _ => ?_` and prove the remaining obligations. Simplify using `[Pi.smul_apply, smul_eq_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fdU_qf_smul {ε : Fin n → Bool} (lam : Fin n → ℝ) (s : ℝ) (y : PCoord ε → ℂ) :
    Qf lam ((s : ℂ) • y) = s ^ 2 * Qf lam y := by
  unfold Qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  simp [Pi.smul_apply, smul_eq_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/- English proof (translation)
Introduce `_ _ _` and use `le_rfl`.
-/
theorem fdU_antitone_zero : Antitone (0 : Fin n → ℝ) := fun _ _ _ => le_rfl

/- English proof (translation)
Rewrite using `[ph_lamT]`. Combine the linear relations using `[ph_nonneg hlam z]`.
-/
theorem fdU_ph_ge {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (t : ℕ) (z : PCoord ε → ℂ) :
    (t : ℝ) * Ph (0 : Fin n → ℝ) (pmat z) ≤ Ph (lamT lam t) (pmat z) := by
  rw [ph_lamT]
  linarith [ph_nonneg hlam z]

/- English proof (translation)
Establish `hrho : rhoP ((s : ℂ) • y) = s * rhoP y` using `by rw [rhoP_real_smul, abs_of_pos hs0]`. Establish `hl` using `ph_lower (lam := (0 : Fin n → ℝ)) fdU_antitone_zero ((s : ℂ) • y) (ep := s * rhoP y) hrho.le hr`. Rewrite `hl` using `[fdU_qf_smul]`. Establish `hg` using `fdU_ph_ge hlam t ((s : ℂ) • y)`. Establish `ht : (0 : ℝ) ≤ t` using `Nat.cast_nonneg t`.

Establish `hQ : (1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y = (t : ℝ) * ((1 - s * rhoP y) * (s ^ 2 * Qf (0 : Fin n → ℝ) y))`. Combine the equalities or inequalities in the displayed calculation. Establish `hm` using `mul_le_mul_of_nonneg_left hl ht`. Establish `h1 : (1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y ≤ 2 * Ph (lamT lam t) (pmat ((s : ℂ) • y))`. Rewrite using `[hQ]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hJ` using `jac_le_exp ((s : ℂ) • y)`. Rewrite `hJ` using `[fdU_sqrt_hs_smul hs0.le]`. Rewrite using `[Real.exp_add]`. Conclude with `mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hJ (le_trans zero_le_one (jac_ge_one _)) (Real.exp_pos _).le`.
-/
theorem fdU_near {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) {s : ℝ} (hs0 : 0 < s) {t : ℕ}
    (hst : s ^ 2 * t = 1) (y : PCoord ε → ℂ) (hr : s * rhoP y ≤ 1) :
    Real.exp (-2 * Ph (lamT lam t) (pmat ((s : ℂ) • y))) * Jac ((s : ℂ) • y) ≤
      Real.exp (-(1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y +
        ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) * (s * Real.sqrt (hs (pmat y)))) := by
  have hrho : rhoP ((s : ℂ) • y) = s * rhoP y := by rw [rhoP_real_smul, abs_of_pos hs0]
  have hl := ph_lower (lam := (0 : Fin n → ℝ)) fdU_antitone_zero ((s : ℂ) • y) (ep := s * rhoP y) hrho.le hr
  rw [fdU_qf_smul] at hl
  have hg := fdU_ph_ge hlam t ((s : ℂ) • y)
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hQ : (1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y =
      (t : ℝ) * ((1 - s * rhoP y) * (s ^ 2 * Qf (0 : Fin n → ℝ) y)) := by
    calc _ = (s ^ 2 * t) * ((1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y) := by rw [hst]; ring
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left hl ht
  have h1 : (1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y ≤ 2 * Ph (lamT lam t) (pmat ((s : ℂ) • y)) := by
    rw [hQ]; linarith
  have hJ := jac_le_exp ((s : ℂ) • y)
  rw [fdU_sqrt_hs_smul hs0.le] at hJ
  rw [Real.exp_add]
  exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hJ (le_trans zero_le_one (jac_ge_one _))
    (Real.exp_pos _).le

/- English proof (translation)
Establish `hhs : hs (pmat y) = Real.sqrt (hs (pmat y)) ^ 2` using `(Real.sq_sqrt (fdU_hs_nonneg y)).symm`. Establish `hm` using `potential_lower_min ((s : ℂ) • y)`. Rewrite `hm` using `[fdU_sqrt_hs_smul hs0.le, fdU_hs_smul]`. Establish `hJ` using `jac_le_exp ((s : ℂ) • y)`. Rewrite `hJ` using `[fdU_sqrt_hs_smul hs0.le]`.

Establish `hPh` using `fdU_ph_ge hlam t ((s : ℂ) • y)`. Use `set k := Real.sqrt (2 * (q0 ε : ℝ)) with hk`. Use `set r := Real.sqrt (hs (pmat y)) with hr`. Use `set X := Real.sqrt (t₀ : ℝ) with hX`. Use `set a := X / k with ha`.

Establish `hk0 : 0 ≤ k` using `Real.sqrt_nonneg _`. Establish `hr0 : 0 ≤ r` using `Real.sqrt_nonneg _`. Establish `hT0 : 0 < X` using `Real.sqrt_pos.mpr (by exact_mod_cast h0)`. Establish `ht0 : (0 : ℝ) ≤ t` using `Nat.cast_nonneg _`. Establish `hsT : s * X ≤ 1`.

Establish `h1 : s ^ 2 * t₀ ≤ 1`. Rewrite using `[← hst]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast ht) (sq_nonneg s)`. Establish `h2 : (s * X) ^ 2 ≤ 1` using `by rw [mul_pow, hX, Real.sq_sqrt (Nat.cast_nonneg _)]; exact h1`. Use polynomial arithmetic with `[mul_pos hs0 hT0]`. Establish `hsinv : X ≤ s⁻¹`.

Combine the equalities or inequalities in the displayed calculation. Establish `hmin : a * r - a ^ 2 / 4 ≤ (t : ℝ) * min (s ^ 2 * hs (pmat y)) (s * r / k)`. Rewrite using `[mul_min_of_nonneg _ _ ht0]`. Use `le_min ?_ ?_` and prove the remaining obligations. Establish `e : (t : ℝ) * (s ^ 2 * hs (pmat y)) = r ^ 2`.

Rewrite using `[hhs]`. Take the linear combination `r ^ 2 * hst`. Rewrite using `[e]`. Use polynomial arithmetic with `[sq_nonneg (r - a / 2)]`. Establish `hrk : 0 ≤ r / k` using `div_nonneg hr0 hk0`.

Establish `e : (t : ℝ) * (s * r / k) = s⁻¹ * (r / k)`. Establish `: s⁻¹ = s * t` using `by field_simp; linear_combination -hst`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `ea : a * r = X * (r / k)` using `by rw [ha]; ring`.

Rewrite using `[e]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hsinv hrk, sq_nonneg a]`. Establish `hs' : s ≤ 1 / X` using `by rw [le_div_iff₀ hT0]; exact hsT`. Establish `hJ2 : ((n : ℝ) - 1) * k * (s * r) ≤ |(n : ℝ) - 1| * k / X * r`. Combine the equalities or inequalities in the displayed calculation.

Establish `hm2` using `mul_le_mul_of_nonneg_left hm ht0`. Establish `hE : -2 * Ph (lamT lam t) (pmat ((s : ℂ) • y)) ≤ a ^ 2 / 32 - a / 8 * r`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fdU_far {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) {t₀ t : ℕ} (h0 : 1 ≤ t₀)
    (ht : t₀ ≤ t) {s : ℝ} (hs0 : 0 < s) (hst : s ^ 2 * t = 1) (y : PCoord ε → ℂ) :
    Real.exp (-2 * Ph (lamT lam t) (pmat ((s : ℂ) • y))) * Jac ((s : ℂ) • y) ≤
      Real.exp ((Real.sqrt t₀ / Real.sqrt (2 * (q0 ε : ℝ))) ^ 2 / 32 -
        (Real.sqrt t₀ / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
          |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt t₀) * Real.sqrt (hs (pmat y))) := by
  have hhs : hs (pmat y) = Real.sqrt (hs (pmat y)) ^ 2 := (Real.sq_sqrt (fdU_hs_nonneg y)).symm
  have hm := potential_lower_min ((s : ℂ) • y)
  rw [fdU_sqrt_hs_smul hs0.le, fdU_hs_smul] at hm
  have hJ := jac_le_exp ((s : ℂ) • y)
  rw [fdU_sqrt_hs_smul hs0.le] at hJ
  have hPh := fdU_ph_ge hlam t ((s : ℂ) • y)
  set k := Real.sqrt (2 * (q0 ε : ℝ)) with hk
  set r := Real.sqrt (hs (pmat y)) with hr
  set X := Real.sqrt (t₀ : ℝ) with hX
  set a := X / k with ha
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hT0 : 0 < X := Real.sqrt_pos.mpr (by exact_mod_cast h0)
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hsT : s * X ≤ 1 := by
    have h1 : s ^ 2 * t₀ ≤ 1 := by
      rw [← hst]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast ht) (sq_nonneg s)
    have h2 : (s * X) ^ 2 ≤ 1 := by rw [mul_pow, hX, Real.sq_sqrt (Nat.cast_nonneg _)]; exact h1
    nlinarith [mul_pos hs0 hT0]
  have hsinv : X ≤ s⁻¹ := by
    calc X = s⁻¹ * (s * X) := by field_simp
      _ ≤ s⁻¹ * 1 := mul_le_mul_of_nonneg_left hsT (inv_nonneg.mpr hs0.le)
      _ = s⁻¹ := mul_one _
  have hmin : a * r - a ^ 2 / 4 ≤ (t : ℝ) * min (s ^ 2 * hs (pmat y)) (s * r / k) := by
    rw [mul_min_of_nonneg _ _ ht0]
    refine le_min ?_ ?_
    · have e : (t : ℝ) * (s ^ 2 * hs (pmat y)) = r ^ 2 := by
        rw [hhs]; linear_combination r ^ 2 * hst
      rw [e]; nlinarith [sq_nonneg (r - a / 2)]
    · have hrk : 0 ≤ r / k := div_nonneg hr0 hk0
      have e : (t : ℝ) * (s * r / k) = s⁻¹ * (r / k) := by
        have : s⁻¹ = s * t := by field_simp; linear_combination -hst
        rw [this]; ring
      have ea : a * r = X * (r / k) := by rw [ha]; ring
      rw [e]; nlinarith [mul_le_mul_of_nonneg_right hsinv hrk, sq_nonneg a]
  have hs' : s ≤ 1 / X := by rw [le_div_iff₀ hT0]; exact hsT
  have hJ2 : ((n : ℝ) - 1) * k * (s * r) ≤ |(n : ℝ) - 1| * k / X * r := by
    calc ((n : ℝ) - 1) * k * (s * r) ≤ |(n : ℝ) - 1| * k * (s * r) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hk0) (by positivity)
      _ ≤ |(n : ℝ) - 1| * k * (1 / X * r) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs' hr0) (by positivity)
      _ = _ := by ring
  have hm2 := mul_le_mul_of_nonneg_left hm ht0
  have hE : -2 * Ph (lamT lam t) (pmat ((s : ℂ) • y)) ≤ a ^ 2 / 32 - a / 8 * r := by
    nlinarith
  calc Real.exp (-2 * Ph (lamT lam t) (pmat ((s : ℂ) • y))) * Jac ((s : ℂ) • y)
      ≤ Real.exp (a ^ 2 / 32 - a / 8 * r) * Real.exp (|(n : ℝ) - 1| * k / X * r) :=
        mul_le_mul (Real.exp_le_exp.mpr hE) (hJ.trans (Real.exp_le_exp.mpr hJ2))
          (le_trans zero_le_one (jac_ge_one _)) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/- English proof (translation)
Establish `h : 0 < Fintype.card (PCoord ε)` using `Fintype.card_pos_iff.mpr ⟨ab⟩`. Rewrite `h` using `[card_PCoord]`. Break down `Nat.eq_zero_or_pos (pOf ε) with hp | hp` into its components or cases. Simplify using `[hp] at h`. Break down `Nat.eq_zero_or_pos (qOf ε) with hq | hq` into its components or cases.

Simplify using `[hq] at h`. Conclude with `le_min hp hq`.
-/
theorem one_le_q0_of_coord {ε : Fin n → Bool} (ab : PCoord ε) : 1 ≤ q0 ε := by
  have h : 0 < Fintype.card (PCoord ε) := Fintype.card_pos_iff.mpr ⟨ab⟩
  rw [card_PCoord] at h
  rcases Nat.eq_zero_or_pos (pOf ε) with hp | hp
  · simp [hp] at h
  rcases Nat.eq_zero_or_pos (qOf ε) with hq | hq
  · simp [hq] at h
  exact le_min hp hq

/- English proof (translation)
The claim follows from `|(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) := by have hq : (1 : ℝ) ≤ q0 ε := by exact_mod_cast one_le_q0_of_coord ab have hn : (1 : ℝ) ≤ n := by have := ab.1.1.pos exact_mod_cast this set k := Real.sqrt (2 * (q0 ε : ℝ)) with hk set X := R …`.
-/
theorem fdU_c_pos {ε : Fin n → Bool} (ab : PCoord ε) :
    0 < Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
      |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) := by
  have hq : (1 : ℝ) ≤ q0 ε := by exact_mod_cast one_le_q0_of_coord ab
  have hn : (1 : ℝ) ≤ n := by
    have := ab.1.1.pos
    exact_mod_cast this
  set k := Real.sqrt (2 * (q0 ε : ℝ)) with hk
  set X := Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) with hX
  have hk0 : 0 < k := Real.sqrt_pos.mpr (by linarith)
  have hX0 : 0 < X := Real.sqrt_pos.mpr (by positivity)
  have hk2 : k ^ 2 = 2 * (q0 ε : ℝ) := Real.sq_sqrt (by linarith)
  have hX2 : X ^ 2 = ((16 * n * q0 ε + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have habs : |(n : ℝ) - 1| = (n : ℝ) - 1 := abs_of_nonneg (by linarith)
  have e : X / k / 8 - |(n : ℝ) - 1| * k / X = (X ^ 2 - 8 * ((n : ℝ) - 1) * k ^ 2) / (8 * k * X) := by
    rw [habs]; field_simp
  rw [e]
  apply div_pos _ (by positivity)
  rw [hX2, hk2]
  push_cast
  nlinarith

/- English proof (translation)
Rewrite using `[← Real.exp_sum]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use `set r := Real.sqrt (hs (pmat y)) with hr`. Establish `hr0 : 0 ≤ r` using `Real.sqrt_nonneg _`. Establish `hle : ∀ ab, ‖y ab‖ ≤ r`.

Introduce `ab`. Use `le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)` and prove the remaining obligations. Rewrite using `[hs_pmat]`. Establish `h1` using `Finset.single_le_sum (f := fun ab => ‖y ab‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ ab)`. Establish `h2 : 0 ≤ ∑ ab, ‖y ab‖ ^ 2` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum : ∑ ab, ‖y ab‖ ≤ (Fintype.card (PCoord ε) : ℝ) * r`. Combine the equalities or inequalities in the displayed calculation. Use `set N := (Fintype.card (PCoord ε) : ℝ) + 1 with hN`. Establish `hN0 : 0 < N` using `by positivity`.

Establish `e : ∑ ab : PCoord ε, -(c / N) * ‖y ab‖ = -(c / N * ∑ ab, ‖y ab‖)`. Rewrite using `[Finset.mul_sum, ← Finset.sum_neg_distrib]`. Simplify using `only [neg_mul]`. Rewrite using `[e]`. Establish `key : c / N * ∑ ab, ‖y ab‖ ≤ c * r`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fdU_exp_le_prod {ε : Fin n → Bool} {c : ℝ} (hc : 0 ≤ c) (y : PCoord ε → ℂ) :
    Real.exp (-c * Real.sqrt (hs (pmat y))) ≤
      ∏ ab : PCoord ε, Real.exp (-(c / ((Fintype.card (PCoord ε) : ℝ) + 1)) * ‖y ab‖) := by
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  set r := Real.sqrt (hs (pmat y)) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hle : ∀ ab, ‖y ab‖ ≤ r := by
    intro ab
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    rw [hs_pmat]
    have h1 := Finset.single_le_sum (f := fun ab => ‖y ab‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ ab)
    have h2 : 0 ≤ ∑ ab, ‖y ab‖ ^ 2 := by positivity
    linarith
  have hsum : ∑ ab, ‖y ab‖ ≤ (Fintype.card (PCoord ε) : ℝ) * r := by
    calc ∑ ab, ‖y ab‖ ≤ ∑ _ab : PCoord ε, r := Finset.sum_le_sum fun ab _ => hle ab
      _ = _ := by simp
  set N := (Fintype.card (PCoord ε) : ℝ) + 1 with hN
  have hN0 : 0 < N := by positivity
  have e : ∑ ab : PCoord ε, -(c / N) * ‖y ab‖ = -(c / N * ∑ ab, ‖y ab‖) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; simp only [neg_mul]
  rw [e]
  have key : c / N * ∑ ab, ‖y ab‖ ≤ c * r := by
    calc c / N * ∑ ab, ‖y ab‖ ≤ c / N * ((Fintype.card (PCoord ε) : ℝ) * r) :=
          mul_le_mul_of_nonneg_left hsum (div_nonneg hc hN0.le)
      _ ≤ c / N * (N * r) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by rw [hN]; linarith) hr0)
            (div_nonneg hc hN0.le)
      _ = c * r := by field_simp
  linarith

end ReciprocityTheory.ChartRestriction.DS.G2
