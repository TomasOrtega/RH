import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementC

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

namespace CurveSer

section Tools

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- English proof (translation)
Establish `h1 : PowerSeries.map φ a * PowerSeries.map φ (invOfUnit a e) = 1`. Rewrite using `[← map_mul, PowerSeries.mul_invOfUnit a e h, map_one]`. Establish `h2 : PowerSeries.map φ a * invOfUnit (PowerSeries.map φ a) (Units.map φ e) = 1`. Apply `PowerSeries.mul_invOfUnit` to reduce the goal to its premises. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h]`.

Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, mul_one]`. Use `_ = (PowerSeries.map φ a * PowerSeries.map φ (invOfUnit a e)) * invOfUnit (PowerSeries.map φ a) (Units.map φ e) := by ring`. Use `_ = invOfUnit (PowerSeries.map φ a) (Units.map φ e) := by rw [h1, one_mul]`.
-/
theorem map_invOfUnit (φ : R →+* S) (a : R⟦X⟧) (e : Rˣ) (h : constantCoeff a = e) :
    PowerSeries.map φ (invOfUnit a e) = invOfUnit (PowerSeries.map φ a) (Units.map φ e) := by
  have h1 : PowerSeries.map φ a * PowerSeries.map φ (invOfUnit a e) = 1 := by
    rw [← map_mul, PowerSeries.mul_invOfUnit a e h, map_one]
  have h2 : PowerSeries.map φ a * invOfUnit (PowerSeries.map φ a) (Units.map φ e) = 1 := by
    apply PowerSeries.mul_invOfUnit
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h]
    simp
  calc PowerSeries.map φ (invOfUnit a e)
      = PowerSeries.map φ (invOfUnit a e) *
          (PowerSeries.map φ a * invOfUnit (PowerSeries.map φ a) (Units.map φ e)) := by
        rw [h2, mul_one]
    _ = (PowerSeries.map φ a * PowerSeries.map φ (invOfUnit a e)) *
          invOfUnit (PowerSeries.map φ a) (Units.map φ e) := by ring
    _ = invOfUnit (PowerSeries.map φ a) (Units.map φ e) := by rw [h1, one_mul]

end Tools

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/- English proof (translation)
The claim follows from `(Formalism.ELL.wSeriesUnique R W).choose_spec.1`.
-/
theorem wSer_fixed : Formalism.ELL.WFixed W (wSer W) := (Formalism.ELL.wSeriesUnique R W).choose_spec.1

/- English proof (translation)
The claim follows from `(Formalism.ELL.wSeriesUnique R W).unique hw (wSer_fixed W)`.
-/
theorem wSer_unique {w : R⟦X⟧} (hw : Formalism.ELL.WFixed W w) : w = wSer W := (Formalism.ELL.wSeriesUnique R W).unique hw (wSer_fixed W)

/- English proof (translation)
The claim follows from `(wSer_fixed W).1`.
-/
theorem wSer_cc : constantCoeff (wSer W) = 0 := (wSer_fixed W).1

/- English proof (translation)
Establish `hfix` using `(wSer_fixed W).2`. Take `⟨v1, hv1⟩` from `(PowerSeries.X_dvd_iff).mpr (wSer_cc W)`. Take `⟨v2, hv2⟩ : X ^ 2 ∣ wSer W` from `⟨X + C W.a₁ * v1 + C W.a₂ * X * v1 + C W.a₃ * v1 ^ 2 + C W.a₄ * X * v1 ^ 2 + C W.a₆ * X * v1 ^ 3, by rw [hfix, hv1]; ring⟩`. Conclude with `⟨1 + C W.a₁ * v2 + C W.a₂ * X * v2 + C W.a₃ * X * v2 ^ 2 + C W.a₄ * X ^ 2 * v2 ^ 2 + C W.a₆ * X ^ 3 * v2 ^ 3, by rw [hfix, hv2]; ring⟩`.
-/
private theorem exists_wSer_eq_X_cube_mul : ∃ v : R⟦X⟧, wSer W = X ^ 3 * v := by
  have hfix := (wSer_fixed W).2
  obtain ⟨v1, hv1⟩ := (PowerSeries.X_dvd_iff).mpr (wSer_cc W)
  obtain ⟨v2, hv2⟩ : X ^ 2 ∣ wSer W := ⟨X + C W.a₁ * v1 + C W.a₂ * X * v1 + C W.a₃ * v1 ^ 2
      + C W.a₄ * X * v1 ^ 2 + C W.a₆ * X * v1 ^ 3, by rw [hfix, hv1]; ring⟩
  exact ⟨1 + C W.a₁ * v2 + C W.a₂ * X * v2 + C W.a₃ * X * v2 ^ 2 + C W.a₄ * X ^ 2 * v2 ^ 2
      + C W.a₆ * X ^ 3 * v2 ^ 3, by rw [hfix, hv2]; ring⟩

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_wSer_eq_X_cube_mul W`. Establish `hu : wU W = v`. Use extensionality with `n`. Unfold `wU`. Rewrite using `[coeff_mk, hv]`.

Simplify using `[coeff_X_pow_mul']`. Rewrite using `[hu]`. Conclude with `hv`.
-/
theorem wSer_eq : wSer W = X ^ 3 * wU W := by
  obtain ⟨v, hv⟩ := exists_wSer_eq_X_cube_mul W
  have hu : wU W = v := by
    ext n
    unfold wU
    rw [coeff_mk, hv]
    simp [coeff_X_pow_mul']
  rw [hu]
  exact hv

/- English proof (translation)
Establish `hfix` using `(wSer_fixed W).2`. Rewrite `hfix` using `[wSer_eq W]`. Establish `e : X ^ 3 + C W.a₁ * X * (X ^ 3 * wU W) + C W.a₂ * X ^ 2 * (X ^ 3 * wU W) + C W.a₃ * (X ^ 3 * wU W) ^ 2 + C W.a₄ * X * (X ^ 3 * wU W) ^ 2 + C W.a₆ * (X ^ 3 * wU W) ^ 3 = X ^ 3 * (1 + X * (C W.a₁ * wU W + C W.a₂ * X * wU W + C W.a₃ * X ^ 2 * wU W ^ 2 + C W.a₄ * X ^ 3 * wU W ^ 2 + …` using `by ring`. Establish `h3` using `congrArg (coeff 3) (hfix.trans e)`. Simplify `h3` using `[coeff_X_pow_mul']`.
-/
theorem wU_cc : constantCoeff (wU W) = 1 := by
  have hfix := (wSer_fixed W).2
  rw [wSer_eq W] at hfix
  have e : X ^ 3 + C W.a₁ * X * (X ^ 3 * wU W) + C W.a₂ * X ^ 2 * (X ^ 3 * wU W)
      + C W.a₃ * (X ^ 3 * wU W) ^ 2 + C W.a₄ * X * (X ^ 3 * wU W) ^ 2
      + C W.a₆ * (X ^ 3 * wU W) ^ 3
      = X ^ 3 * (1 + X * (C W.a₁ * wU W + C W.a₂ * X * wU W + C W.a₃ * X ^ 2 * wU W ^ 2
        + C W.a₄ * X ^ 3 * wU W ^ 2 + C W.a₆ * X ^ 5 * wU W ^ 3)) := by ring
  have h3 := congrArg (coeff 3) (hfix.trans e)
  simpa [coeff_X_pow_mul'] using h3

/- English proof (translation)
The claim follows from `PowerSeries.mul_invOfUnit (wU W) 1 (by rw [wU_cc W, Units.val_one])`.
-/
theorem wU_mul_xS : wU W * xS W = 1 := PowerSeries.mul_invOfUnit (wU W) 1 (by rw [wU_cc W, Units.val_one])

/- English proof (translation)
Establish `h` using `congrArg constantCoeff (wU_mul_xS W)`. Rewrite `h` using `[map_mul, wU_cc W, one_mul, map_one]`. Conclude with `h`.
-/
theorem xS_cc : constantCoeff (xS W) = 1 := by
  have h := congrArg constantCoeff (wU_mul_xS W)
  rw [map_mul, wU_cc W, one_mul, map_one] at h
  exact h

/- English proof (translation)
Unfold `yS`. Rewrite using `[map_neg, xS_cc W]`.
-/
theorem yS_cc : constantCoeff (yS W) = -1 := by
  unfold yS
  rw [map_neg, xS_cc W]

/- English proof (translation)
Unfold `fw`. Simplify using `[wSer_cc W]`.
-/
theorem fw_cc : constantCoeff (fw W) = 1 := by
  unfold fw
  simp [wSer_cc W]

/- English proof (translation)
The claim follows from `PowerSeries.mul_invOfUnit (fw W) 1 (by rw [fw_cc W, Units.val_one])`.
-/
theorem fw_mul_om : fw W * om W = 1 := PowerSeries.mul_invOfUnit (fw W) 1 (by rw [fw_cc W, Units.val_one])

/- English proof (translation)
Establish `h` using `congrArg constantCoeff (fw_mul_om W)`. Rewrite `h` using `[map_mul, fw_cc W, one_mul, map_one]`. Conclude with `h`.
-/
theorem om_cc : constantCoeff (om W) = 1 := by
  have h := congrArg constantCoeff (fw_mul_om W)
  rw [map_mul, fw_cc W, one_mul, map_one] at h
  exact h

/- English proof (translation)
Unfold `fw`. Take the linear combination `(-2 * C W.a₃ - 2 * C W.a₄ * X - 3 * C W.a₆ * wSer W) * wSer_eq W`.
-/
theorem fw_eq : fw W = 1 - C W.a₁ * X - C W.a₂ * X ^ 2
    - X ^ 3 * (2 * C W.a₃ * wU W + 2 * C W.a₄ * X * wU W + 3 * C W.a₆ * wU W * wSer W) := by
  unfold fw
  linear_combination (-2 * C W.a₃ - 2 * C W.a₄ * X - 3 * C W.a₆ * wSer W) * wSer_eq W

/- English proof (translation)
Rewrite using `[fw_eq W]`. Simplify using `[coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_one, coeff_C_mul]`.
-/
theorem fw_coeff_one : coeff 1 (fw W) = -W.a₁ := by
  rw [fw_eq W]
  simp [coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_one, coeff_C_mul]

/- English proof (translation)
Rewrite using `[fw_eq W]`. Simplify using `[coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_one, coeff_C_mul]`.
-/
theorem fw_coeff_two : coeff 2 (fw W) = -W.a₂ := by
  rw [fw_eq W]
  simp [coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_one, coeff_C_mul]

/- English proof (translation)
Establish `h` using `congrArg (coeff 1) (fw_mul_om W)`. Simplify using `[coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, fw_cc W, om_cc W, fw_coeff_one W, coeff_one] at h`. Use `first`. Consider the case `linear_combination h`. Consider the case `linear_combination -h`.
-/
theorem om_coeff_one : coeff 1 (om W) = W.a₁ := by
  have h := congrArg (coeff 1) (fw_mul_om W)
  simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    fw_cc W, om_cc W, fw_coeff_one W, coeff_one] at h
  first
    | linear_combination h
    | linear_combination -h

/- English proof (translation)
Establish `h` using `congrArg (coeff 2) (fw_mul_om W)`. Simplify using `[coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, fw_cc W, om_cc W, fw_coeff_one W, fw_coeff_two W, om_coeff_one W, coeff_one] at h`. Use `first`. Consider the case `linear_combination h`. Consider the case `linear_combination -h`.
-/
theorem om_coeff_two : coeff 2 (om W) = W.a₁ ^ 2 + W.a₂ := by
  have h := congrArg (coeff 2) (fw_mul_om W)
  simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    fw_cc W, om_cc W, fw_coeff_one W, fw_coeff_two W, om_coeff_one W, coeff_one] at h
  first
    | linear_combination h
    | linear_combination -h

/- English proof (translation)
Unfold `iDen`. Simplify using `[wSer_cc W]`.
-/
theorem iDen_cc : constantCoeff (iDen W) = -1 := by
  unfold iDen
  simp [wSer_cc W]

/- English proof (translation)
The claim follows from `PowerSeries.mul_invOfUnit (iDen W) (-1) (by rw [iDen_cc W, Units.val_neg, Units.val_one])`.
-/
theorem iDen_mul_inv : iDen W * invOfUnit (iDen W) (-1) = 1 := PowerSeries.mul_invOfUnit (iDen W) (-1) (by rw [iDen_cc W, Units.val_neg, Units.val_one])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem D_apply (f : R⟦X⟧) : D W f = fw W * derivative R f := rfl

/- English proof (translation)
Establish `h` using `congrArg (derivative R) (wSer_fixed W).2`. Simplify using `[Derivation.leibniz, Derivation.leibniz_pow, derivative_C, derivative_X, smul_eq_mul, nsmul_eq_mul] at h`. Unfold `fw fu`. Take the linear combination `h`.
-/
theorem deriv_wSer_mul_fw : derivative R (wSer W) * fw W = fu W := by
  have h := congrArg (derivative R) (wSer_fixed W).2
  simp [Derivation.leibniz, Derivation.leibniz_pow, derivative_C, derivative_X, smul_eq_mul,
    nsmul_eq_mul] at h
  unfold fw fu
  linear_combination h

/- English proof (translation)
Rewrite using `[D_apply, ← mul_assoc, mul_comm (om W), fw_mul_om W, one_mul]`.
-/
theorem om_mul_D (f : R⟦X⟧) : om W * D W f = derivative R f := by
  rw [D_apply, ← mul_assoc, mul_comm (om W), fw_mul_om W, one_mul]

section Map

variable {S : Type v} [CommRing S] (φ : R →+* S)

/- English proof (translation)
Use `wSer_unique (W.map φ) ?_` and prove the remaining obligations. Unfold `Formalism.ELL.WFixed`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, wSer_cc W, map_zero]`. Use `conv_lhs => rw [(wSer_fixed W).2]`.

Simplify using the standard rewrite rules.
-/
theorem map_wSer : PowerSeries.map φ (wSer W) = wSer (W.map φ) := by
  refine wSer_unique (W.map φ) ?_
  unfold Formalism.ELL.WFixed
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      wSer_cc W, map_zero]
  · conv_lhs => rw [(wSer_fixed W).2]
    simp

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [wU, coeff_map, coeff_mk, ← map_wSer W φ]`.
-/
theorem map_wU : PowerSeries.map φ (wU W) = wU (W.map φ) := by
  ext n
  simp only [wU, coeff_map, coeff_mk, ← map_wSer W φ]

/- English proof (translation)
Unfold `xS`. Rewrite using `[map_invOfUnit φ (wU W) 1 (by rw [wU_cc W, Units.val_one]), map_wU W φ, map_one]`.
-/
theorem map_xS : PowerSeries.map φ (xS W) = xS (W.map φ) := by
  unfold xS
  rw [map_invOfUnit φ (wU W) 1 (by rw [wU_cc W, Units.val_one]), map_wU W φ, map_one]

/- English proof (translation)
Unfold `yS`. Rewrite using `[map_neg, map_xS W φ]`.
-/
theorem map_yS : PowerSeries.map φ (yS W) = yS (W.map φ) := by
  unfold yS
  rw [map_neg, map_xS W φ]

/- English proof (translation)
Establish `h2 : PowerSeries.map φ (2 : R⟦X⟧) = 2`. Rewrite using `[show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]`. Evaluate the numerical expressions. Establish `h3 : PowerSeries.map φ (3 : R⟦X⟧) = 3`. Rewrite using `[show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]`.

Evaluate the numerical expressions. Unfold `fw`. Simplify using `[map_wSer W φ, h2, h3]`.
-/
theorem map_fw : PowerSeries.map φ (fw W) = fw (W.map φ) := by
  have h2 : PowerSeries.map φ (2 : R⟦X⟧) = 2 := by
    rw [show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  have h3 : PowerSeries.map φ (3 : R⟦X⟧) = 3 := by
    rw [show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  unfold fw
  simp [map_wSer W φ, h2, h3]

/- English proof (translation)
Establish `h2 : PowerSeries.map φ (2 : R⟦X⟧) = 2`. Rewrite using `[show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]`. Evaluate the numerical expressions. Establish `h3 : PowerSeries.map φ (3 : R⟦X⟧) = 3`. Rewrite using `[show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]`.

Evaluate the numerical expressions. Unfold `fu`. Simplify using `[map_wSer W φ, h2, h3]`.
-/
theorem map_fu : PowerSeries.map φ (fu W) = fu (W.map φ) := by
  have h2 : PowerSeries.map φ (2 : R⟦X⟧) = 2 := by
    rw [show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  have h3 : PowerSeries.map φ (3 : R⟦X⟧) = 3 := by
    rw [show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  unfold fu
  simp [map_wSer W φ, h2, h3]

/- English proof (translation)
Unfold `om`. Rewrite using `[map_invOfUnit φ (fw W) 1 (by rw [fw_cc W, Units.val_one]), map_fw W φ, map_one]`.
-/
theorem map_om : PowerSeries.map φ (om W) = om (W.map φ) := by
  unfold om
  rw [map_invOfUnit φ (fw W) 1 (by rw [fw_cc W, Units.val_one]), map_fw W φ, map_one]

/- English proof (translation)
Unfold `iDen`. Simplify using `[map_wSer W φ]`.
-/
theorem map_iDen : PowerSeries.map φ (iDen W) = iDen (W.map φ) := by
  unfold iDen
  simp [map_wSer W φ]

/- English proof (translation)
Establish `hu : Units.map (φ : R →* S) (-1) = -1` using `Units.ext (by simp)`. Unfold `iSer`. Rewrite using `[map_mul, map_X, map_invOfUnit φ (iDen W) (-1) (by rw [iDen_cc W, Units.val_neg, Units.val_one]), map_iDen W φ, hu]`.
-/
theorem map_iSer : PowerSeries.map φ (iSer W) = iSer (W.map φ) := by
  have hu : Units.map (φ : R →* S) (-1) = -1 := Units.ext (by simp)
  unfold iSer
  rw [map_mul, map_X, map_invOfUnit φ (iDen W) (-1) (by rw [iDen_cc W, Units.val_neg, Units.val_one]),
    map_iDen W φ, hu]

end Map

end CurveSer

open CurveSer

/- English proof (translation)
Unfold `WSerSpec`. Introduce `R _ W`. Conclude with `⟨wSer_fixed W, fun w hw => wSer_unique W hw⟩`.
-/
theorem w_series_spec : WSerSpec.{u} := by
  unfold WSerSpec
  intro R _ W
  exact ⟨wSer_fixed W, fun w hw => wSer_unique W hw⟩

/- English proof (translation)
Unfold `WSerFactor`. Introduce `R _ W`. Conclude with `⟨wSer_eq W, wU_cc W, wU_mul_xS W, xS_cc W, yS_cc W⟩`.
-/
theorem w_series_factorization : WSerFactor.{u} := by
  unfold WSerFactor
  intro R _ W
  exact ⟨wSer_eq W, wU_cc W, wU_mul_xS W, xS_cc W, yS_cc W⟩

/- English proof (translation)
Unfold `UnitSpec`. Introduce `R _ W`. Conclude with `⟨fw_cc W, fw_mul_om W, om_cc W, om_coeff_one W, om_coeff_two W, iDen_cc W, iDen_mul_inv W⟩`.
-/
theorem invariant_differential_units : UnitSpec.{u} := by
  unfold UnitSpec
  intro R _ W
  exact ⟨fw_cc W, fw_mul_om W, om_cc W, om_coeff_one W, om_coeff_two W, iDen_cc W, iDen_mul_inv W⟩

/- English proof (translation)
Unfold `SeriesMap`. Introduce `R S _ _ φ W`. Conclude with `⟨map_wSer W φ, map_wU W φ, map_xS W φ, map_yS W φ, map_fw W φ, map_fu W φ, map_om W φ, map_iSer W φ⟩`.
-/
theorem series_map : SeriesMap.{u, v} := by
  unfold SeriesMap
  intro R S _ _ φ W
  exact ⟨map_wSer W φ, map_wU W φ, map_xS W φ, map_yS W φ, map_fw W φ, map_fu W φ, map_om W φ,
    map_iSer W φ⟩

/- English proof (translation)
Unfold `FlowU`. Introduce `R _ W`. Establish `hfw : fwAt (curveS W) X (wSer W) = fw W`. Unfold `fwAt fw`. Simplify using the standard rewrite rules.

Establish `hfu : fuAt (curveS W) X (wSer W) = fu W`. Unfold `fuAt fu`. Simplify using the standard rewrite rules. Use `⟨?_, ?_, ?_, hfw, hfu, om_mul_D W⟩` and prove the remaining obligations. Unfold `IsDer`.

Conclude with `⟨fun a b => map_add (D W) a b, fun a b => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]⟩`. Unfold `ConstCurve`. Simplify using `[D_apply]`. Unfold `IsFlowUW`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `WEq`. Simplify using `using (wSer_fixed W).2`. Rewrite using `[D_apply, derivative_X, mul_one, hfw]`. Rewrite using `[D_apply, mul_comm, deriv_wSer_mul_fw W, hfu]`.
-/
theorem unit_flow : FlowU.{u} := by
  unfold FlowU
  intro R _ W
  have hfw : fwAt (curveS W) X (wSer W) = fw W := by
    unfold fwAt fw
    simp
  have hfu : fuAt (curveS W) X (wSer W) = fu W := by
    unfold fuAt fu
    simp
  refine ⟨?_, ?_, ?_, hfw, hfu, om_mul_D W⟩
  · unfold IsDer
    exact ⟨fun a b => map_add (D W) a b, fun a b => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]⟩
  · unfold ConstCurve
    simp [D_apply]
  · unfold IsFlowUW
    refine ⟨?_, ?_, ?_⟩
    · unfold WEq
      simpa using (wSer_fixed W).2
    · rw [D_apply, derivative_X, mul_one, hfw]
    · rw [D_apply, mul_comm, deriv_wSer_mul_fw W, hfu]

end Formalism.L2.Th1.A
