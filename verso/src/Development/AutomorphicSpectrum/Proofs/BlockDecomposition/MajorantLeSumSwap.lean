import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern

open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B

noncomputable section

namespace GlobalTheory.CompanionTheory.MajC

/- English proof (translation)
Unfold `kern`. Use `mul_nonneg (by positivity) (le_min ?_ ?_)` and prove the remaining obligations. Conclude with `Real.rpow_nonneg (by positivity) _`. Conclude with `Real.rpow_nonneg (by positivity) _`.
-/
theorem kern_nonneg' (s T : ℝ) (hT : 0 < T) (z : ℂ) : 0 ≤ kern s T z := by
  unfold kern
  refine mul_nonneg (by positivity) (le_min ?_ ?_)
  · exact Real.rpow_nonneg (by positivity) _
  · exact Real.rpow_nonneg (by positivity) _

/- English proof (translation)
Unfold `gm`. Use `split_ifs with hc`. Establish `h1 : 0 ≤ β ^ (-ε)` using `Real.rpow_nonneg hβ.le _`. Establish `h2 : 0 ≤ ‖h 0 0‖ ^ (-4 + ε)` using `Real.rpow_nonneg (norm_nonneg _) _`. Establish `h3` using `kern_nonneg' ε β hβ (h 1 1 - h 1 0 / h 0 0 * h 0 1)`.

Check the signs of the components of the expression. Conclude with `le_rfl`.
-/
theorem gm_nonneg' (ε β : ℝ) (m : ℕ) (hβ : 0 < β) (h : M22) : 0 ≤ gm ε β m h := by
  unfold gm
  split_ifs with hc
  · have h1 : 0 ≤ β ^ (-ε) := Real.rpow_nonneg hβ.le _
    have h2 : 0 ≤ ‖h 0 0‖ ^ (-4 + ε) := Real.rpow_nonneg (norm_nonneg _) _
    have h3 := kern_nonneg' ε β hβ (h 1 1 - h 1 0 / h 0 0 * h 0 1)
    positivity
  · exact le_rfl

/- English proof (translation)
Establish `hw : 0 < β / r` using `div_pos hβ hr`. Use `set a := r ^ ε with ha`. Use `set b := β ^ ε with hb`. Establish `ha0 : 0 < a` using `Real.rpow_pos_of_pos hr _`. Establish `hb0 : 0 < b` using `Real.rpow_pos_of_pos hβ _`.

Use `set W := (1 + β / r) ^ N with hWdef`. Establish `hW1 : 1 ≤ W` using `one_le_pow₀ (by linarith)`. Establish `hW0 : 0 < W` using `by linarith`. Establish `e1 : (β / r) ^ ε = b / a` using `Real.div_rpow hβ.le hr.le _`. Establish `e2 : (r / β) ^ ε = a / b` using `Real.div_rpow hr.le hβ.le _`.

Establish `e3 : r ^ (-(2 + ε)) = (r ^ 2)⁻¹ * a⁻¹`. Rewrite using `[neg_add, Real.rpow_add hr, Real.rpow_neg hr.le, Real.rpow_neg hr.le, Real.rpow_two]`. Establish `e4 : β ^ (-ε) = b⁻¹` using `Real.rpow_neg hβ.le _`. Establish `hW2 : (b / a) ^ 2 ≤ W`. Establish `s1 : (b / a) ^ 2 = (β / r) ^ (2 * ε)`.

Rewrite using `[← e1, mul_comm, Real.rpow_mul hw.le, Real.rpow_two]`. Establish `s2 : (β / r) ^ (2 * ε) ≤ (1 + β / r) ^ (2 * ε)` using `Real.rpow_le_rpow hw.le (by linarith) (by positivity)`. Establish `s3 : (1 + β / r) ^ (2 * ε) ≤ (1 + β / r) ^ (N : ℝ)` using `Real.rpow_le_rpow_of_exponent_le (by linarith) hN`. Rewrite `s3` using `[Real.rpow_natCast]`. Rewrite using `[s1]`.

Conclude with `s2.trans s3`. Rewrite using `[e1, e2, e3, e4]`. Establish `hr2 : 0 < (r ^ 2)⁻¹` using `by positivity`. Establish `key : a⁻¹ * W⁻¹ ≤ b⁻¹ * min (a / b) (b / a)`. Rewrite using `[mul_min_of_nonneg _ _ (by positivity)]`.

Use `le_min ?_ ?_` and prove the remaining obligations. Establish `: W⁻¹ ≤ ((b / a) ^ 2)⁻¹` using `inv_anti₀ (by positivity) hW2`. Combine the equalities or inequalities in the displayed calculation. Establish `: W⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ hW1`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem radial_bound (ε β r : ℝ) (N : ℕ) (hε : 0 < ε) (hβ : 0 < β) (hr : 0 < r)
    (hN : 2 * ε ≤ N) :
    r ^ (-(2 + ε)) * ((1 + β / r) ^ N)⁻¹ ≤
      β ^ (-ε) * ((r ^ 2)⁻¹ * min ((r / β) ^ ε) ((β / r) ^ ε)) := by
  have hw : 0 < β / r := div_pos hβ hr
  set a := r ^ ε with ha
  set b := β ^ ε with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos hr _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hβ _
  set W := (1 + β / r) ^ N with hWdef
  have hW1 : 1 ≤ W := one_le_pow₀ (by linarith)
  have hW0 : 0 < W := by linarith
  have e1 : (β / r) ^ ε = b / a := Real.div_rpow hβ.le hr.le _
  have e2 : (r / β) ^ ε = a / b := Real.div_rpow hr.le hβ.le _
  have e3 : r ^ (-(2 + ε)) = (r ^ 2)⁻¹ * a⁻¹ := by
    rw [neg_add, Real.rpow_add hr, Real.rpow_neg hr.le, Real.rpow_neg hr.le, Real.rpow_two]
  have e4 : β ^ (-ε) = b⁻¹ := Real.rpow_neg hβ.le _
  have hW2 : (b / a) ^ 2 ≤ W := by
    have s1 : (b / a) ^ 2 = (β / r) ^ (2 * ε) := by
      rw [← e1, mul_comm, Real.rpow_mul hw.le, Real.rpow_two]
    have s2 : (β / r) ^ (2 * ε) ≤ (1 + β / r) ^ (2 * ε) :=
      Real.rpow_le_rpow hw.le (by linarith) (by positivity)
    have s3 : (1 + β / r) ^ (2 * ε) ≤ (1 + β / r) ^ (N : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hN
    rw [Real.rpow_natCast] at s3
    rw [s1]
    exact s2.trans s3
  rw [e1, e2, e3, e4]
  have hr2 : 0 < (r ^ 2)⁻¹ := by positivity
  have key : a⁻¹ * W⁻¹ ≤ b⁻¹ * min (a / b) (b / a) := by
    rw [mul_min_of_nonneg _ _ (by positivity)]
    refine le_min ?_ ?_
    · have : W⁻¹ ≤ ((b / a) ^ 2)⁻¹ := inv_anti₀ (by positivity) hW2
      calc a⁻¹ * W⁻¹ ≤ a⁻¹ * ((b / a) ^ 2)⁻¹ := by gcongr
        _ = b⁻¹ * (a / b) := by field_simp
    · have : W⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
      calc a⁻¹ * W⁻¹ ≤ a⁻¹ * 1 := by gcongr
        _ = b⁻¹ * (b / a) := by field_simp
  calc (r ^ 2)⁻¹ * a⁻¹ * W⁻¹ = (r ^ 2)⁻¹ * (a⁻¹ * W⁻¹) := by ring
    _ ≤ (r ^ 2)⁻¹ * (b⁻¹ * min (a / b) (b / a)) := by gcongr
    _ = b⁻¹ * ((r ^ 2)⁻¹ * min (a / b) (b / a)) := by ring

/- English proof (translation)
Unfold `dt`. Rewrite using `[Matrix.det_fin_two]`. Simplify using `[Matrix.of_apply]`.
-/
theorem dt_eq (h : M22) : dt h = ‖h 0 0 * h 1 1 - h 0 1 * h 1 0‖ := by
  unfold dt
  rw [Matrix.det_fin_two]
  simp [Matrix.of_apply]

/- English proof (translation)
Rewrite using `[dt_eq, dt_eq]`. Establish `: (swp h) 0 0 * (swp h) 1 1 - (swp h) 0 1 * (swp h) 1 0 = -(h 0 0 * h 1 1 - h 0 1 * h 1 0)`. Simplify using `[swp]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, norm_neg]`.
-/
theorem dt_swp (h : M22) : dt (swp h) = dt h := by
  rw [dt_eq, dt_eq]
  have : (swp h) 0 0 * (swp h) 1 1 - (swp h) 0 1 * (swp h) 1 0
      = -(h 0 0 * h 1 1 - h 0 1 * h 1 0) := by
    simp [swp]; ring
  rw [this, norm_neg]

/- English proof (translation)
Simplify using `[col, swp, max_comm]`.
-/
theorem col_swp (h : M22) : col (swp h) = col h := by
  simp [col, swp, max_comm]

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Simplify `norm_le_pi_norm h 1` using `[swp]`. Simplify `norm_le_pi_norm h 0` using `[swp]`.
-/
theorem norm_swp_le (h : M22) : ‖swp h‖ ≤ ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  fin_cases i
  · simpa [swp] using norm_le_pi_norm h 1
  · simpa [swp] using norm_le_pi_norm h 0

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [swp]`.
-/
theorem swp_swp (h : M22) : swp (swp h) = h := by
  funext i
  fin_cases i <;> simp [swp]

/- English proof (translation)
The claim follows from `le_antisymm (norm_swp_le h) (by simpa [swp_swp] using norm_swp_le (swp h))`.
-/
theorem norm_swp (h : M22) : ‖swp h‖ = ‖h‖ :=
  le_antisymm (norm_swp_le h) (by simpa [swp_swp] using norm_swp_le (swp h))

/- English proof (translation)
Unfold `hm`. Rewrite using `[dt_swp, col_swp, norm_swp]`.
-/
theorem hm_swp (ε β : ℝ) (N : ℕ) (h : M22) : hm ε N β (swp h) = hm ε N β h := by
  unfold hm
  rw [dt_swp, col_swp, norm_swp]

/- English proof (translation)
The claim follows from `(norm_le_pi_norm (h i) j).trans (norm_le_pi_norm h i)`.
-/
theorem entry_le (h : M22) (i j : Fin 2) : ‖h i j‖ ≤ ‖h‖ :=
  (norm_le_pi_norm (h i) j).trans (norm_le_pi_norm h i)

/- English proof (translation)
Establish `hu : h 0 0 ≠ 0`. Introduce `hu`. Establish `hv0 : h 1 0 = 0`. Rewrite `hv` using `[hu, norm_zero]`. Conclude with `norm_le_zero_iff.1 hv`.

Apply `hd` to reduce the goal to its premises. Rewrite using `[dt_eq, hu, hv0]`. Simplify using the standard rewrite rules. Use `set z := h 1 1 - h 1 0 / h 0 0 * h 0 1 with hz`. Establish `hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = h 0 0 * z`.

Rewrite using `[hz]`. Clear the denominators using the available nonvanishing facts. Establish `hU : 0 < ‖h 0 0‖` using `norm_pos_iff.2 hu`. Establish `hdt : dt h = ‖h 0 0‖ * ‖z‖` using `by rw [dt_eq, hdet, norm_mul]`. Establish `hr : 0 < ‖z‖`.

Establish `: 0 < dt h` using `lt_of_le_of_ne (by rw [dt_eq]; exact norm_nonneg _) (Ne.symm hd)`. Rewrite `this` using `[hdt]`. Conclude with `(pos_iff_pos_of_mul_pos this).1 hU`. Establish `hcol : col h = ‖h 0 0‖` using `max_eq_left hv`. Establish `hgm : gm ε β m h = β ^ (-ε) * ‖h 0 0‖ ^ (-4 + ε) * ((1 + ‖h 0 0‖) ^ m)⁻¹ * ((1 + ‖h 0 1‖) ^ m)⁻¹ * kern ε β z`.

Unfold `gm`. Rewrite using `[if_pos ⟨hv, hu⟩]`. Rewrite using `[hgm]`. Establish `hfrac : β * (‖h 0 0‖ / (‖h 0 0‖ * ‖z‖)) = β / ‖z‖` using `by field_simp`. Establish `hpow : (‖h 0 0‖ * ‖z‖) ^ (-(2 + ε)) * ‖h 0 0‖ ^ (-2 + 2 * ε) = ‖h 0 0‖ ^ (-4 + ε) * ‖z‖ ^ (-(2 + ε))`.

Rewrite using `[Real.mul_rpow hU.le hr.le, mul_right_comm, ← Real.rpow_add hU]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hA : ((1 + ‖h‖) ^ N)⁻¹ ≤ ((1 + ‖h 0 0‖) ^ m)⁻¹ * ((1 + ‖h 0 1‖) ^ m)⁻¹`. Rewrite using `[← mul_inv]`.

Apply `inv_anti₀ (by positivity)` to reduce the goal to its premises. Establish `h1 : 1 + ‖h 0 0‖ ≤ 1 + ‖h‖` using `by linarith [entry_le h 0 0]`. Establish `h2 : 1 + ‖h 0 1‖ ≤ 1 + ‖h‖` using `by linarith [entry_le h 0 1]`. Establish `h3 : (1 : ℝ) ≤ 1 + ‖h‖` using `by linarith [norm_nonneg h]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hN' : 2 * ε ≤ (N : ℝ)`. Establish `: (m : ℝ) ≤ N`. Establish `: m ≤ N` using `by omega`. Conclude with `this` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hB` using `radial_bound ε β ‖z‖ N hε hβ hr hN'`. Establish `hk : kern ε β z = (‖z‖ ^ 2)⁻¹ * min ((‖z‖ / β) ^ ε) ((β / ‖z‖) ^ ε)` using `rfl`. Unfold `hm`. Rewrite using `[hdt, hcol, hfrac, hpow, hk]`. Establish `hUp : 0 ≤ ‖h 0 0‖ ^ (-4 + ε)` using `Real.rpow_nonneg hU.le _`.

Establish `hzp : 0 ≤ ‖z‖ ^ (-(2 + ε)) * ((1 + β / ‖z‖) ^ N)⁻¹`. Use `Real.rpow_nonneg hr.le (-(2 + ε))` as an intermediate fact. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left ?_ hUp` and prove the remaining obligations.

Conclude with `mul_le_mul hA hB hzp (by positivity)`. Use `_ = _ := by ring`.
-/
theorem one_region (ε β : ℝ) (m N : ℕ) (hε : 0 < ε) (hβ : 0 < β) (hm' : 2 * ε ≤ m)
    (hN : 2 * m ≤ N) (h : M22) (hv : ‖h 1 0‖ ≤ ‖h 0 0‖) (hd : dt h ≠ 0) :
    hm ε N β h ≤ gm ε β m h := by
  have hu : h 0 0 ≠ 0 := by
    intro hu
    have hv0 : h 1 0 = 0 := by
      rw [hu, norm_zero] at hv
      exact norm_le_zero_iff.1 hv
    apply hd
    rw [dt_eq, hu, hv0]
    simp
  set z := h 1 1 - h 1 0 / h 0 0 * h 0 1 with hz
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = h 0 0 * z := by
    rw [hz]; field_simp
  have hU : 0 < ‖h 0 0‖ := norm_pos_iff.2 hu
  have hdt : dt h = ‖h 0 0‖ * ‖z‖ := by rw [dt_eq, hdet, norm_mul]
  have hr : 0 < ‖z‖ := by
    have : 0 < dt h := lt_of_le_of_ne (by rw [dt_eq]; exact norm_nonneg _) (Ne.symm hd)
    rw [hdt] at this
    exact (pos_iff_pos_of_mul_pos this).1 hU
  have hcol : col h = ‖h 0 0‖ := max_eq_left hv
  have hgm : gm ε β m h = β ^ (-ε) * ‖h 0 0‖ ^ (-4 + ε) * ((1 + ‖h 0 0‖) ^ m)⁻¹ *
      ((1 + ‖h 0 1‖) ^ m)⁻¹ * kern ε β z := by
    unfold gm
    rw [if_pos ⟨hv, hu⟩]
  rw [hgm]
  have hfrac : β * (‖h 0 0‖ / (‖h 0 0‖ * ‖z‖)) = β / ‖z‖ := by field_simp
  have hpow : (‖h 0 0‖ * ‖z‖) ^ (-(2 + ε)) * ‖h 0 0‖ ^ (-2 + 2 * ε)
      = ‖h 0 0‖ ^ (-4 + ε) * ‖z‖ ^ (-(2 + ε)) := by
    rw [Real.mul_rpow hU.le hr.le, mul_right_comm, ← Real.rpow_add hU]
    congr 2
    ring
  have hA : ((1 + ‖h‖) ^ N)⁻¹ ≤ ((1 + ‖h 0 0‖) ^ m)⁻¹ * ((1 + ‖h 0 1‖) ^ m)⁻¹ := by
    rw [← mul_inv]
    apply inv_anti₀ (by positivity)
    have h1 : 1 + ‖h 0 0‖ ≤ 1 + ‖h‖ := by linarith [entry_le h 0 0]
    have h2 : 1 + ‖h 0 1‖ ≤ 1 + ‖h‖ := by linarith [entry_le h 0 1]
    have h3 : (1 : ℝ) ≤ 1 + ‖h‖ := by linarith [norm_nonneg h]
    calc (1 + ‖h 0 0‖) ^ m * (1 + ‖h 0 1‖) ^ m
        ≤ (1 + ‖h‖) ^ m * (1 + ‖h‖) ^ m := by gcongr
      _ = (1 + ‖h‖) ^ (2 * m) := by rw [two_mul, pow_add]
      _ ≤ (1 + ‖h‖) ^ N := pow_le_pow_right₀ h3 hN
  have hN' : 2 * ε ≤ (N : ℝ) := by
    have : (m : ℝ) ≤ N := by
      have : m ≤ N := by omega
      exact_mod_cast this
    linarith
  have hB := radial_bound ε β ‖z‖ N hε hβ hr hN'
  have hk : kern ε β z = (‖z‖ ^ 2)⁻¹ * min ((‖z‖ / β) ^ ε) ((β / ‖z‖) ^ ε) := rfl
  unfold hm
  rw [hdt, hcol, hfrac, hpow, hk]
  have hUp : 0 ≤ ‖h 0 0‖ ^ (-4 + ε) := Real.rpow_nonneg hU.le _
  have hzp : 0 ≤ ‖z‖ ^ (-(2 + ε)) * ((1 + β / ‖z‖) ^ N)⁻¹ := by
    have := Real.rpow_nonneg hr.le (-(2 + ε))
    positivity
  calc ‖h 0 0‖ ^ (-4 + ε) * ‖z‖ ^ (-(2 + ε)) * ((1 + ‖h‖) ^ N)⁻¹ * ((1 + β / ‖z‖) ^ N)⁻¹
      = ‖h 0 0‖ ^ (-4 + ε) * (((1 + ‖h‖) ^ N)⁻¹ *
          (‖z‖ ^ (-(2 + ε)) * ((1 + β / ‖z‖) ^ N)⁻¹)) := by ring
    _ ≤ ‖h 0 0‖ ^ (-4 + ε) * ((((1 + ‖h 0 0‖) ^ m)⁻¹ * ((1 + ‖h 0 1‖) ^ m)⁻¹) *
          (β ^ (-ε) * ((‖z‖ ^ 2)⁻¹ * min ((‖z‖ / β) ^ ε) ((β / ‖z‖) ^ ε)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hUp
        exact mul_le_mul hA hB hzp (by positivity)
    _ = _ := by ring

/- English proof (translation)
Establish `g1` using `gm_nonneg' ε β m hβ h`. Establish `g2` using `gm_nonneg' ε β m hβ (swp h)`. Distinguish the cases in `hd : dt h = 0`. Establish `: hm ε N β h = 0`. Unfold `hm`.

Rewrite using `[hd, Real.zero_rpow (by linarith)]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `add_nonneg g1 g2`. Distinguish the cases in `hv : ‖h 1 0‖ ≤ ‖h 0 0‖`.

Use `one_region ε β m N hε hβ hm' hN h hv hd` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv' : ‖(swp h) 1 0‖ ≤ ‖(swp h) 0 0‖`. Establish `: ‖h 0 0‖ ≤ ‖h 1 0‖` using `(not_le.1 hv).le`. Simplify `this` using `[swp]`.

Use `one_region ε β m N hε hβ hm' hN (swp h) hv' (by rw [dt_swp]; exact hd)` as an intermediate fact. Rewrite `this` using `[hm_swp]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hm_le_gm_add (ε β : ℝ) (m N : ℕ) (hε : 0 < ε) (hβ : 0 < β) (hm' : 2 * ε ≤ m)
    (hN : 2 * m ≤ N) (h : M22) : hm ε N β h ≤ gm ε β m h + gm ε β m (swp h) := by
  have g1 := gm_nonneg' ε β m hβ h
  have g2 := gm_nonneg' ε β m hβ (swp h)
  by_cases hd : dt h = 0
  · have : hm ε N β h = 0 := by
      unfold hm
      rw [hd, Real.zero_rpow (by linarith)]
      simp
    rw [this]
    exact add_nonneg g1 g2
  by_cases hv : ‖h 1 0‖ ≤ ‖h 0 0‖
  · have := one_region ε β m N hε hβ hm' hN h hv hd
    linarith
  · have hv' : ‖(swp h) 1 0‖ ≤ ‖(swp h) 0 0‖ := by
      have : ‖h 0 0‖ ≤ ‖h 1 0‖ := (not_le.1 hv).le
      simpa [swp] using this
    have := one_region ε β m N hε hβ hm' hN (swp h) hv' (by rw [dt_swp]; exact hd)
    rw [hm_swp] at this
    linarith

end GlobalTheory.CompanionTheory.MajC
