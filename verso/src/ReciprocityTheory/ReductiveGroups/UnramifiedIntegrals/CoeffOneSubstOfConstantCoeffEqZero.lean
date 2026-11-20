import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgDefs

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Field
variable {K : Type} [Field K] (g2 g3 : K)

/- English proof (translation)
Establish `hs : HasSubst g` using `HasSubst.of_constantCoeff_zero hg`. Establish `hX : X ∣ g` using `X_dvd_iff.mpr hg`. Rewrite using `[PowerSeries.coeff_subst' hs, finsum_eq_single _ 1]`. Simplify using `[smul_eq_mul]`. Introduce `d hd`.

Break down `Nat.lt_or_gt_of_ne hd with h | h` into its components or cases. Establish `: d = 0` using `by omega`. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Establish `h2 : X ^ d ∣ g ^ d` using `pow_dvd_pow_of_dvd hX d`.

Establish `h3` using `X_pow_dvd_iff.mp h2 1 h`. Simplify using `[h3]`.
-/
theorem coeff_one_subst_of_constantCoeff_eq_zero (f g : PowerSeries K) (hg : constantCoeff g = 0) :
    coeff 1 (f.subst g) = coeff 1 f * coeff 1 g := by
  have hs : HasSubst g := HasSubst.of_constantCoeff_zero hg
  have hX : X ∣ g := X_dvd_iff.mpr hg
  rw [PowerSeries.coeff_subst' hs, finsum_eq_single _ 1]
  · simp [smul_eq_mul]
  · intro d hd
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have : d = 0 := by omega
      subst this
      simp
    · have h2 : X ^ d ∣ g ^ d := pow_dvd_pow_of_dvd hX d
      have h3 := X_pow_dvd_iff.mp h2 1 h
      simp [h3]

/- English proof (translation)
Unfold `uSer`. Rewrite using `[map_mul, map_mul, constantCoeff_X, zero_mul, zero_mul]`.
-/
theorem uSer_const : constantCoeff (uSer g2 g3) = 0 := by
  unfold uSer
  rw [map_mul, map_mul, constantCoeff_X, zero_mul, zero_mul]
/- English proof (translation)
Unfold `uSer`. Rewrite using `[mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_inv]`. Unfold `wpNum wpDen`. Simplify using `[← coeff_zero_eq_constantCoeff_apply]`.
-/
theorem uSer_coeff_one : coeff 1 (uSer g2 g3) = 1 := by
  unfold uSer
  rw [mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
    map_mul, constantCoeff_inv]
  unfold wpNum wpDen
  simp [← coeff_zero_eq_constantCoeff_apply]

/- English proof (translation)
Rewrite using `[uSer_coeff_one]`. Conclude with `isUnit_one`.
-/
theorem isUnit_coeff_one_weierstrassExp : IsUnit (coeff 1 (uSer g2 g3)) := by
  rw [uSer_coeff_one]
  exact isUnit_one

/- English proof (translation)
Assemble the required witnesses or components as `⟨(uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3), PowerSeries.constantCoeff_substInvOfIsUnit _ _, PowerSeries.subst_substInvOfIsUnit_right _ (uSer_const g2 g3) _⟩`.
-/
theorem exists_rightInverse_weierstrassExp : ∃ t : PowerSeries K, constantCoeff t = 0 ∧ (uSer g2 g3).subst t = X := ⟨(uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3), PowerSeries.constantCoeff_substInvOfIsUnit _ _,
  PowerSeries.subst_substInvOfIsUnit_right _ (uSer_const g2 g3) _⟩

/- English proof (translation)
Unfold `lgS`. Rewrite using `[dif_pos (exists_rightInverse_weierstrassExp g2 g3)]`. Conclude with `(exists_rightInverse_weierstrassExp g2 g3).choose_spec.1`.
-/
theorem lgS_const : constantCoeff (lgS g2 g3) = 0 := by
  unfold lgS
  rw [dif_pos (exists_rightInverse_weierstrassExp g2 g3)]
  exact (exists_rightInverse_weierstrassExp g2 g3).choose_spec.1
/- English proof (translation)
Unfold `lgS`. Rewrite using `[dif_pos (exists_rightInverse_weierstrassExp g2 g3)]`. Conclude with `(exists_rightInverse_weierstrassExp g2 g3).choose_spec.2`.
-/
theorem uSer_subst_lgS : (uSer g2 g3).subst (lgS g2 g3) = X := by
  unfold lgS
  rw [dif_pos (exists_rightInverse_weierstrassExp g2 g3)]
  exact (exists_rightInverse_weierstrassExp g2 g3).choose_spec.2
/- English proof (translation)
Establish `h` using `congrArg (coeff 1) (uSer_subst_lgS g2 g3)`. Rewrite `h` using `[coeff_one_subst_of_constantCoeff_eq_zero _ _ (lgS_const g2 g3), uSer_coeff_one, one_mul]`. Simplify using `using h`.
-/
theorem lgS_coeff_one : coeff 1 (lgS g2 g3) = 1 := by
  have h := congrArg (coeff 1) (uSer_subst_lgS g2 g3)
  rw [coeff_one_subst_of_constantCoeff_eq_zero _ _ (lgS_const g2 g3), uSer_coeff_one, one_mul] at h
  simpa using h

/- English proof (translation)
Establish `h1` using `PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero (uSer_const g2 g3)) (HasSubst.of_constantCoeff_zero ht) ((uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3))`. Rewrite `h1` using `[PowerSeries.subst_substInvOfIsUnit_left _ (uSer_const g2 g3), PowerSeries.subst_X (HasSubst.of_constantCoeff_zero ht), h, PowerSeries.X_subst]`. Conclude with `h1`.
-/
theorem eq_substInv_of_rightInverse (t : PowerSeries K) (ht : constantCoeff t = 0)
    (h : (uSer g2 g3).subst t = X) :
    t = (uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3) := by
  have h1 := PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero (uSer_const g2 g3))
    (HasSubst.of_constantCoeff_zero ht) ((uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3))
  rw [PowerSeries.subst_substInvOfIsUnit_left _ (uSer_const g2 g3), PowerSeries.subst_X (HasSubst.of_constantCoeff_zero ht),
    h, PowerSeries.X_subst] at h1
  exact h1

/- English proof (translation)
The claim follows from `eq_substInv_of_rightInverse g2 g3 (lgS g2 g3) (lgS_const g2 g3) (uSer_subst_lgS g2 g3)`.
-/
theorem weierstrassLog_eq_substInv : lgS g2 g3 = (uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3) := eq_substInv_of_rightInverse g2 g3 (lgS g2 g3) (lgS_const g2 g3) (uSer_subst_lgS g2 g3)

/- English proof (translation)
Rewrite using `[weierstrassLog_eq_substInv]`. Conclude with `PowerSeries.subst_substInvOfIsUnit_left _ (uSer_const g2 g3) _`.
-/
theorem lgS_subst_uSer : (lgS g2 g3).subst (uSer g2 g3) = X := by
  rw [weierstrassLog_eq_substInv]
  exact PowerSeries.subst_substInvOfIsUnit_left _ (uSer_const g2 g3) _

/- English proof (translation)
Conclude with `(eq_substInv_of_rightInverse g2 g3 t ht h).trans (weierstrassLog_eq_substInv g2 g3).symm`.
-/
theorem lgS_unique (t : PowerSeries K) (ht : constantCoeff t = 0) (h : (uSer g2 g3).subst t = X) :
    t = lgS g2 g3 := by
  exact (eq_substInv_of_rightInverse g2 g3 t ht h).trans (weierstrassLog_eq_substInv g2 g3).symm

/- English proof (translation)
Rewrite using `[map_mul, constantCoeff_C, lgS_const, mul_zero]`.
-/
theorem constantCoeff_C_mul_weierstrassLog (b : K) : constantCoeff (C b * lgS g2 g3) = 0 := by
  rw [map_mul, constantCoeff_C, lgS_const, mul_zero]

/- English proof (translation)
Establish `hs` using `constantCoeff_C_mul_weierstrassLog g2 g3 b`. Establish `ha : HasSubst (C b * lgS g2 g3)` using `HasSubst.of_constantCoeff_zero hs`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst' ha, finsum_eq_single _ 0]`. Simplify using `[uSer_const]`. Introduce `d hd`.

Simplify using `[map_pow, hs, zero_pow hd]`.
-/
theorem mult_const (b : K) : constantCoeff ((uSer g2 g3).subst (C b * lgS g2 g3)) = 0 := by
  have hs := constantCoeff_C_mul_weierstrassLog g2 g3 b
  have ha : HasSubst (C b * lgS g2 g3) := HasSubst.of_constantCoeff_zero hs
  rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst' ha, finsum_eq_single _ 0]
  · simp [uSer_const]
  · intro d hd
    simp [map_pow, hs, zero_pow hd]
/- English proof (translation)
Establish `hu` using `HasSubst.of_constantCoeff_zero (uSer_const g2 g3)`. Establish `ha` using `HasSubst.of_constantCoeff_zero (constantCoeff_C_mul_weierstrassLog g2 g3 b)`. Establish `h1` using `PowerSeries.subst_comp_subst_apply hu ha (lgS g2 g3)`. Rewrite `h1` using `[lgS_subst_uSer, PowerSeries.subst_X ha]`. Conclude with `h1.symm`.
-/
theorem mult_log (b : K) :
    (lgS g2 g3).subst ((uSer g2 g3).subst (C b * lgS g2 g3)) = C b * lgS g2 g3 := by
  have hu := HasSubst.of_constantCoeff_zero (uSer_const g2 g3)
  have ha := HasSubst.of_constantCoeff_zero (constantCoeff_C_mul_weierstrassLog g2 g3 b)
  have h1 := PowerSeries.subst_comp_subst_apply hu ha (lgS g2 g3)
  rw [lgS_subst_uSer, PowerSeries.subst_X ha] at h1
  exact h1.symm
/- English proof (translation)
Establish `hl` using `HasSubst.of_constantCoeff_zero (lgS_const g2 g3)`. Establish `hE` using `HasSubst.of_constantCoeff_zero he`. Establish `h1` using `PowerSeries.subst_comp_subst_apply hl hE (uSer g2 g3)`. Rewrite `h1` using `[uSer_subst_lgS, PowerSeries.subst_X hE, h]`. Conclude with `h1`.
-/
theorem mult_unique (b : K) (e : PowerSeries K) (he : constantCoeff e = 0)
    (h : (lgS g2 g3).subst e = C b * lgS g2 g3) : e = (uSer g2 g3).subst (C b * lgS g2 g3) := by
  have hl := HasSubst.of_constantCoeff_zero (lgS_const g2 g3)
  have hE := HasSubst.of_constantCoeff_zero he
  have h1 := PowerSeries.subst_comp_subst_apply hl hE (uSer g2 g3)
  rw [uSer_subst_lgS, PowerSeries.subst_X hE, h] at h1
  exact h1

/- English proof (translation)
Apply the tactic sequence `first | unfold Formalism.G.ltLog | unfold Formalism.L2.Th1.CM.ltLog`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_mk, dif_neg]`. Introduce and unpack `⟨j, hj⟩`. Establish `h0 : 0 < (l ^ 2) ^ j` using `pow_pos (pow_pos (by omega) 2) j`. Rewrite `h0` using `[← hj]`.

Conclude with `lt_irrefl 0 h0`.
-/
theorem ltLog_const (l : ℕ) (hl : 2 ≤ l) : constantCoeff (ltLog K l) = 0 := by
  first | unfold Formalism.G.ltLog | unfold Formalism.L2.Th1.CM.ltLog
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, dif_neg]
  rintro ⟨j, hj⟩
  have h0 : 0 < (l ^ 2) ^ j := pow_pos (pow_pos (by omega) 2) j
  rw [← hj] at h0
  exact lt_irrefl 0 h0

end Field

section Map
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K)

/- English proof (translation)
Rewrite using `[cW]`. Use `first`. Consider the case `(rw [Nat.strongRecOn_beta]; rfl)`. Consider the case `(rw [Nat.strongRecOn'_beta]; rfl)`. Consider the case `(rw [Nat.strongRecOn_eq]; rfl)`.

Consider the case `(unfold Nat.strongRecOn; rw [Nat.strongRec_eq]; rfl)`. Consider the case `(exact (Nat.strongRecOn_beta' ..).trans rfl)`.
-/
theorem cW_unfold {K : Type} [Field K] (g2 g3 : K) (k : ℕ) : cW g2 g3 k =
    if k = 2 then g2 / 20 else if k = 3 then g3 / 28 else
    if 4 ≤ k then
      3 / ((2 * (k : K) + 1) * ((k : K) - 3)) *
        ∑ m : Fin (k - 3), cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2))
    else 0 := by
  rw [cW]
  first
    | (rw [Nat.strongRecOn_beta]; rfl)
    | (rw [Nat.strongRecOn'_beta]; rfl)
    | (rw [Nat.strongRecOn_eq]; rfl)
    | (unfold Nat.strongRecOn; rw [Nat.strongRec_eq]; rfl)
    | (exact (Nat.strongRecOn_beta' ..).trans rfl)

/- English proof (translation)
Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Rewrite using `[cW_unfold, cW_unfold (φ g2) (φ g3)]`. Use `split_ifs with h1 h2 h3`. Rewrite using `[map_div₀]`.

Use `congr 1`. Conclude with `map_natCast φ 20` after adjusting the coercions. Rewrite using `[map_div₀]`. Use `congr 1`. Conclude with `map_natCast φ 28` after adjusting the coercions.

Simplify using `only [map_mul, map_div₀, map_sum, map_ofNat, map_natCast, map_sub, map_add, map_one]`. Use `congr 1`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `hm` using `m.2`. Rewrite using `[ih _ (by omega), ih _ (by omega)]`.

Simplify using the standard rewrite rules.
-/
theorem cW_map (k : ℕ) : φ (cW g2 g3 k) = cW (φ g2) (φ g3) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [cW_unfold, cW_unfold (φ g2) (φ g3)]
    split_ifs with h1 h2 h3
    · rw [map_div₀]
      congr 1
      exact_mod_cast map_natCast φ 20
    · rw [map_div₀]
      congr 1
      exact_mod_cast map_natCast φ 28
    · simp only [map_mul, map_div₀, map_sum, map_ofNat, map_natCast, map_sub, map_add, map_one]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      have hm := m.2
      rw [ih _ (by omega), ih _ (by omega)]
    · simp

/- English proof (translation)
Use extensionality with `n`. Unfold `wpNum`. Rewrite using `[coeff_map, coeff_mk, coeff_mk]`. Apply the tactic sequence `split_ifs <;> simp [cW_map]`.
-/
theorem wpNum_map : PowerSeries.map φ (wpNum g2 g3) = wpNum (φ g2) (φ g3) := by
  ext n
  unfold wpNum
  rw [coeff_map, coeff_mk, coeff_mk]
  split_ifs <;> simp [cW_map]

/- English proof (translation)
Use extensionality with `n`. Unfold `wpDen`. Rewrite using `[coeff_map, coeff_mk, coeff_mk]`. Apply the tactic sequence `split_ifs <;> simp [cW_map]`.
-/
theorem wpDen_map : PowerSeries.map φ (wpDen g2 g3) = wpDen (φ g2) (φ g3) := by
  ext n
  unfold wpDen
  rw [coeff_map, coeff_mk, coeff_mk]
  split_ifs <;> simp [cW_map]

/- English proof (translation)
Unfold `wpDen`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_mk]`. Simplify using the standard rewrite rules.
-/
theorem wpDen_const' {K : Type} [Field K] (g2 g3 : K) : constantCoeff (wpDen g2 g3) = 1 := by
  unfold wpDen
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
  simp

/- English proof (translation)
Establish `hD : constantCoeff (wpDen (φ g2) (φ g3)) ≠ 0` using `by rw [wpDen_const']; exact one_ne_zero`. Establish `hD0 : constantCoeff (wpDen g2 g3) ≠ 0` using `by rw [wpDen_const']; exact one_ne_zero`. Establish `h : map φ (wpDen g2 g3)⁻¹ = (wpDen (φ g2) (φ g3))⁻¹`. Rewrite using `[PowerSeries.eq_inv_iff_mul_eq_one hD, ← wpDen_map, ← map_mul, PowerSeries.inv_mul_cancel _ hD0, map_one]`. Unfold `uSer`.

Rewrite using `[map_mul, map_mul, map_X, wpNum_map, h]`.
-/
theorem uSer_map : PowerSeries.map φ (uSer g2 g3) = uSer (φ g2) (φ g3) := by
  have hD : constantCoeff (wpDen (φ g2) (φ g3)) ≠ 0 := by rw [wpDen_const']; exact one_ne_zero
  have hD0 : constantCoeff (wpDen g2 g3) ≠ 0 := by rw [wpDen_const']; exact one_ne_zero
  have h : map φ (wpDen g2 g3)⁻¹ = (wpDen (φ g2) (φ g3))⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one hD, ← wpDen_map, ← map_mul,
      PowerSeries.inv_mul_cancel _ hD0, map_one]
  unfold uSer
  rw [map_mul, map_mul, map_X, wpNum_map, h]

/- English proof (translation)
Use `erw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero ha)]`. Apply the tactic sequence `try rfl`.
-/
theorem map_subst_ps {a : PowerSeries K} (ha : constantCoeff a = 0) (f : PowerSeries K) :
    PowerSeries.map φ (f.subst a) = (PowerSeries.map φ f).subst (PowerSeries.map φ a) := by
  erw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero ha)]
  try rfl

/- English proof (translation)
Use `lgS_unique (φ g2) (φ g3) _ ?_ ?_` and prove the remaining obligations. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, lgS_const, map_zero]`. Rewrite using `[← uSer_map, ← map_subst_ps φ (lgS_const g2 g3), uSer_subst_lgS, map_X]`.
-/
theorem lgS_map : PowerSeries.map φ (lgS g2 g3) = lgS (φ g2) (φ g3) := by
  refine lgS_unique (φ g2) (φ g3) _ ?_ ?_
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      lgS_const, map_zero]
  · rw [← uSer_map, ← map_subst_ps φ (lgS_const g2 g3), uSer_subst_lgS, map_X]

/- English proof (translation)
Use extensionality with `n`. Apply the tactic sequence `first | unfold Formalism.G.ltLog | unfold Formalism.L2.Th1.CM.ltLog`. Rewrite using `[coeff_map, coeff_mk, coeff_mk]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ltLog_map (l : ℕ) : PowerSeries.map φ (ltLog K l) = ltLog L l := by
  ext n
  first | unfold Formalism.G.ltLog | unfold Formalism.L2.Th1.CM.ltLog
  rw [coeff_map, coeff_mk, coeff_mk]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[map_subst_ps φ (constantCoeff_C_mul_weierstrassLog g2 g3 b), uSer_map, map_mul, map_C, lgS_map]`.
-/
theorem mult_map (b : K) :
    PowerSeries.map φ ((uSer g2 g3).subst (C b * lgS g2 g3))
      = (uSer (φ g2) (φ g3)).subst (C (φ b) * lgS (φ g2) (φ g3)) := by
  rw [map_subst_ps φ (constantCoeff_C_mul_weierstrassLog g2 g3 b), uSer_map, map_mul, map_C, lgS_map]

/- English proof (translation)
Establish `h0 : constantCoeff (C ε * ltLog K l) = 0`. Rewrite using `[map_mul, constantCoeff_C, ltLog_const l hl, mul_zero]`. Rewrite using `[map_subst_ps φ h0, uSer_map, map_mul, map_C, ltLog_map]`.
-/
theorem lt_map (l : ℕ) (hl : 2 ≤ l) (ε : K) :
    PowerSeries.map φ ((uSer g2 g3).subst (C ε * ltLog K l))
      = (uSer (φ g2) (φ g3)).subst (C (φ ε) * ltLog L l) := by
  have h0 : constantCoeff (C ε * ltLog K l) = 0 := by
    rw [map_mul, constantCoeff_C, ltLog_const l hl, mul_zero]
  rw [map_subst_ps φ h0, uSer_map, map_mul, map_C, ltLog_map]

end Map

/- English proof (translation)
Unfold `omegaK`. Establish `h4 : (((d + 1) / 4 : ℕ) : ℂ) = ((d : ℂ) + 1) / 4`. Establish `h : 4 ∣ d + 1` using `by omega`. Rewrite using `[Nat.cast_div h (by norm_num)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hs : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 = (d : ℂ)`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Use `norm_cast`. Rewrite using `[h4]`.

Take the linear combination `(((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq - (1 / 4 : ℂ) * hs`.
-/
theorem omegaK_quad (d : ℕ) (hd : d % 4 = 3) :
    omegaK d ^ 2 - omegaK d + (((d + 1) / 4 : ℕ) : ℂ) = 0 := by
  unfold omegaK
  have h4 : (((d + 1) / 4 : ℕ) : ℂ) = ((d : ℂ) + 1) / 4 := by
    have h : 4 ∣ d + 1 := by omega
    rw [Nat.cast_div h (by norm_num)]
    push_cast
    ring
  have hs : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    norm_cast
  rw [h4]
  linear_combination (((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq - (1 / 4 : ℂ) * hs

end ReciprocityTheory.ChartRestriction.L1
