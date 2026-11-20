import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalA
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementE

noncomputable section

namespace Formalism.L2.Th1.B.SAdd

open Formalism.InvariantFactorPaths.G7 (at1)

section One

open PowerSeries

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_X_pow_mul']`. Distinguish the cases in `h : 2 ≤ n`. Rewrite using `[if_pos h, divByXSq, coeff_mk, Nat.sub_add_cancel h]`. Rewrite using `[if_neg h]`.

Establish `: n = 0 ∨ n = 1` using `by omega`. Break down `this with rfl | rfl` into its components or cases. Rewrite using `[coeff_zero_eq_constantCoeff_apply, h0]`. Conclude with `h1`.
-/
theorem eq_X_sq_mul_quotient {w : PowerSeries K} (h0 : constantCoeff w = 0) (h1 : coeff 1 w = 0) :
    w = X ^ 2 * divByXSq w := by
  ext n
  rw [coeff_X_pow_mul']
  by_cases h : 2 ≤ n
  · rw [if_pos h, divByXSq, coeff_mk, Nat.sub_add_cancel h]
  · rw [if_neg h]
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · rw [coeff_zero_eq_constantCoeff_apply, h0]
    · exact h1

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, divByXSq, coeff_mk, zero_add, h2]`.
-/
theorem constantCoeff_quotient_X_sq {w : PowerSeries K} (h2 : coeff 2 w = 1) :
    constantCoeff (divByXSq w) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, divByXSq, coeff_mk, zero_add, h2]

/- English proof (translation)
Establish `h : constantCoeff (fLog (divByXSq w)) = 0` using `constantCoeff_fLog (constantCoeff_quotient_X_sq h2)`. Rewrite using `[map_mul, h, mul_zero]`.
-/
theorem constantCoeff_half_log {w : PowerSeries K} (h2 : coeff 2 w = 1) :
    constantCoeff (C (1 / 2 : K) * fLog (divByXSq w)) = 0 := by
  have h : constantCoeff (fLog (divByXSq w)) = 0 := constantCoeff_fLog (constantCoeff_quotient_X_sq h2)
  rw [map_mul, h, mul_zero]

/- English proof (translation)
Establish `hL` using `constantCoeff_half_log h2`. Establish `hadd : C (1 / 2 : K) * fLog (divByXSq w) + C (1 / 2 : K) * fLog (divByXSq w) = fLog (divByXSq w)`. Rewrite using `[← add_mul, ← map_add, add_halves, map_one, one_mul]`. Establish `hE` using `fExp_add (K := K) (ι := Unit) hL hL`. Rewrite `hE` using `[hadd, fExp_fLog (constantCoeff_quotient_X_sq h2)]`.

Use `conv_rhs => rw [eq_X_sq_mul_quotient h0 h1, hE]`. Rewrite using `[sW]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sW_sq {w : PowerSeries K} (h0 : constantCoeff w = 0) (h1 : coeff 1 w = 0)
    (h2 : coeff 2 w = 1) : sW w ^ 2 = w := by
  have hL := constantCoeff_half_log h2
  have hadd : C (1 / 2 : K) * fLog (divByXSq w) + C (1 / 2 : K) * fLog (divByXSq w) = fLog (divByXSq w) := by
    rw [← add_mul, ← map_add, add_halves, map_one, one_mul]
  have hE := fExp_add (K := K) (ι := Unit) hL hL
  rw [hadd, fExp_fLog (constantCoeff_quotient_X_sq h2)] at hE
  conv_rhs => rw [eq_X_sq_mul_quotient h0 h1, hE]
  rw [sW]
  ring

/- English proof (translation)
Rewrite using `[sW, map_mul, constantCoeff_X, zero_mul]`.
-/
theorem constantCoeff_sW (w : PowerSeries K) : constantCoeff (sW w) = 0 := by
  rw [sW, map_mul, constantCoeff_X, zero_mul]

/- English proof (translation)
Rewrite using `[sW, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]`. Conclude with `constantCoeff_fExp (constantCoeff_half_log h2)`.
-/
theorem coeff_one_sW {w : PowerSeries K} (h2 : coeff 2 w = 1) : coeff 1 (sW w) = 1 := by
  rw [sW, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  exact constantCoeff_fExp (constantCoeff_half_log h2)

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, dz, coeff_derivative, zero_add, coeff_one_sW h2]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_dz_sW {w : PowerSeries K} (h2 : coeff 2 w = 1) :
    constantCoeff (dz (sW w)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, dz, coeff_derivative, zero_add, coeff_one_sW h2]
  simp

end One

/- English proof (translation)
Introduce `K _ _ A kap w hw`. Take `⟨hw1, -⟩` from `wSecond K A kap w hw`. Take `⟨hw0, hw2, hwE⟩` from `hw`. Establish `hsq` using `sW_sq hw0 hw1 hw2`. Establish `hd : 2 * sW w * dz (sW w) = dz w`.

Rewrite using `[← dz_sq, hsq]`. Establish `hwne : w ≠ 0`. Introduce `h`. Rewrite `hw2` using `[h, map_zero]`. Conclude with `zero_ne_one hw2`.

Establish `h4 : (4 : PowerSeries K) ≠ 0`. Introduce `h`. Use `congrArg PowerSeries.constantCoeff h` as an intermediate fact. Rewrite `this` using `[map_ofNat, map_zero]`. Conclude with `absurd this (by norm_num)`.

Establish `hs1 : dz (sW w) ^ 2 = 1 + PowerSeries.C A * w + PowerSeries.C kap * w ^ 2`. Use `mul_left_cancel₀ (mul_ne_zero h4 hwne) ?_` and prove the remaining obligations. Take the linear combination `(-4 * dz (sW w) ^ 2) * hsq + (2 * sW w * dz (sW w) + dz w) * hd + hwE`. Establish `hds : dz (sW w) ≠ 0`. Introduce `h`.

Use `constantCoeff_dz_sW hw2` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `zero_ne_one this`. Use `⟨hsq, constantCoeff_sW w, coeff_one_sW hw2, hd, hs1, ?_⟩` and prove the remaining obligations. Establish `h5` using `congrArg dz hs1`.

Rewrite `h5` using `[dz_sq, dz_add, dz_add, dz_one, dz_mul, dz_mul, dz_C, dz_C, dz_sq]`. Use `mul_left_cancel₀ (mul_ne_zero two_ne hds) ?_` and prove the remaining obligations. Take the linear combination `h5 - (PowerSeries.C A + 2 * PowerSeries.C kap * w) * hd`.
-/
theorem sigma_rules_hold : SRules := by
  intro K _ _ A kap w hw
  obtain ⟨hw1, -⟩ := wSecond K A kap w hw
  obtain ⟨hw0, hw2, hwE⟩ := hw
  have hsq := sW_sq hw0 hw1 hw2
  have hd : 2 * sW w * dz (sW w) = dz w := by
    rw [← dz_sq, hsq]
  have hwne : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hw2
    exact zero_ne_one hw2
  have h4 : (4 : PowerSeries K) ≠ 0 := by
    intro h
    have := congrArg PowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at this
    exact absurd this (by norm_num)
  have hs1 : dz (sW w) ^ 2 = 1 + PowerSeries.C A * w + PowerSeries.C kap * w ^ 2 := by
    refine mul_left_cancel₀ (mul_ne_zero h4 hwne) ?_
    linear_combination (-4 * dz (sW w) ^ 2) * hsq + (2 * sW w * dz (sW w) + dz w) * hd + hwE
  have hds : dz (sW w) ≠ 0 := by
    intro h
    have := constantCoeff_dz_sW hw2
    rw [h, map_zero] at this
    exact zero_ne_one this
  refine ⟨hsq, constantCoeff_sW w, coeff_one_sW hw2, hd, hs1, ?_⟩
  have h5 := congrArg dz hs1
  rw [dz_sq, dz_add, dz_add, dz_one, dz_mul, dz_mul, dz_C, dz_C, dz_sq] at h5
  refine mul_left_cancel₀ (mul_ne_zero two_ne hds) ?_
  linear_combination h5 - (PowerSeries.C A + 2 * PowerSeries.C kap * w) * hd

/- English proof (translation)
Establish `key : ∀ j : ℕ, ∀ n : Fin 2 →₀ ℕ, n 1 = j → MvPowerSeries.coeff n k = 0`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => exact fun n hn => coeff_eq_zero_of_eval_second_zero h0 n hn`. Consider the case `succ j ih`.

Introduce `n hn`. Establish `hle : Finsupp.single (1 : Fin 2) 1 ≤ n`. Rewrite using `[Finsupp.single_le_iff]`. Use linear arithmetic over natural numbers and integers. Use `set m := n - Finsupp.single (1 : Fin 2) 1 with hm`.

Establish `hmn : m + Finsupp.single 1 1 = n`. Rewrite using `[hm, tsub_add_cancel_of_le hle]`. Establish `hm1 : m 1 = j` using `by simp [hm, hn]`. Establish `e` using `congrArg (MvPowerSeries.coeff m) hk`. Rewrite `e` using `[MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, hmn, ih (m + Finsupp.single 0 1) (by simp [hm1]), zero_mul]`.

Break down `mul_eq_zero.mp e.symm with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h (Nat.cast_add_one_ne_zero _)`. Use extensionality with `n`. Rewrite using `[map_zero]`.

Conclude with `key _ n rfl`.
-/
theorem eq_zero_of_shear {K : Type} [Field K] [CharZero K] {k : MvPowerSeries (Fin 2) K}
    (hk : pd 0 k = pd 1 k) (h0 : ev0 k = 0) : k = 0 := by
  have key : ∀ j : ℕ, ∀ n : Fin 2 →₀ ℕ, n 1 = j → MvPowerSeries.coeff n k = 0 := by
    intro j
    induction j with
    | zero => exact fun n hn => coeff_eq_zero_of_eval_second_zero h0 n hn
    | succ j ih =>
      intro n hn
      have hle : Finsupp.single (1 : Fin 2) 1 ≤ n := by
        rw [Finsupp.single_le_iff]; omega
      set m := n - Finsupp.single (1 : Fin 2) 1 with hm
      have hmn : m + Finsupp.single 1 1 = n := by
        rw [hm, tsub_add_cancel_of_le hle]
      have hm1 : m 1 = j := by simp [hm, hn]
      have e := congrArg (MvPowerSeries.coeff m) hk
      rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, hmn,
        ih (m + Finsupp.single 0 1) (by simp [hm1]), zero_mul] at e
      rcases mul_eq_zero.mp e.symm with h | h
      · exact h
      · exact absurd h (Nat.cast_add_one_ne_zero _)
  ext n
  rw [map_zero]
  exact key _ n rfl

/- English proof (translation)
Introduce `K _ _ h hh`. Establish `hk : pd 0 (h - atS (ev0 h)) = pd 1 (h - atS (ev0 h))`. Rewrite using `[Add1.pd_sub, Add1.pd_sub, pd_atS, pd_atS, hh]`. Establish `h0 : ev0 (h - atS (ev0 h)) = 0`. Rewrite using `[eval_second_zero_sub, eval_second_zero_at_sum, sub_self]`.

Conclude with `sub_eq_zero.mp (eq_zero_of_shear hk h0)`.
-/
theorem shear_two_variables_holds : ShearTwo := by
  intro K _ _ h hh
  have hk : pd 0 (h - atS (ev0 h)) = pd 1 (h - atS (ev0 h)) := by
    rw [Add1.pd_sub, Add1.pd_sub, pd_atS, pd_atS, hh]
  have h0 : ev0 (h - atS (ev0 h)) = 0 := by
    rw [eval_second_zero_sub, eval_second_zero_at_sum, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_shear hk h0)

section Two

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Rewrite using `[eval_second_zero_eq_algHom, map_one]`.
-/
theorem eval_second_zero_one : ev0 (1 : MvPowerSeries (Fin 2) K) = 1 := by
  rw [eval_second_zero_eq_algHom, map_one]

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)` using `PowerSeries.HasSubst.of_constantCoeff_zero (by simp)`. Rewrite using `[atS, atS, ← PowerSeries.coe_substAlgHom hs, map_pow]`.
-/
theorem atS_sq (f : PowerSeries K) : atS (f ^ 2) = atS f ^ 2 := by
  have hs : PowerSeries.HasSubst
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [atS, atS, ← PowerSeries.coe_substAlgHom hs, map_pow]

/- English proof (translation)
Take the linear combination `(2 * k * x * y * y ^ 2) * hx - (2 * k * x * y * x ^ 2) * hy`.
-/
theorem shear_alg {R : Type} [CommRing R] (k a x y x1 y1 : R)
    (hx : x1 ^ 2 = 1 + a * x ^ 2 + k * (x ^ 2) ^ 2)
    (hy : y1 ^ 2 = 1 + a * y ^ 2 + k * (y ^ 2) ^ 2) :
    (1 - k * x ^ 2 * y ^ 2) *
        (y * ((a + 2 * k * x ^ 2) * x) - x * ((a + 2 * k * y ^ 2) * y)) =
      (x * y1 + y * x1) *
        (-(k * (2 * x * x1) * y ^ 2) + k * x ^ 2 * (2 * y * y1)) := by
  linear_combination (2 * k * x * y * y ^ 2) * hx - (2 * k * x * y * x ^ 2) * hy

end Two

/- English proof (translation)
Introduce `K _ _ A kap w hw`. Take `⟨h1, h2, h3, h4, h5, h6⟩` from `sigma_rules_hold K A kap w hw`. Take `⟨hw0, hw2, -⟩` from `hw`. Establish `E1 : ∀ i : Fin 2, at1 i w = at1 i (sW w) ^ 2`. Introduce `i`.

Use `congrArg (at1 i) h1` as an intermediate fact. Simplify `this.symm` using `only [Add1.triple_lintegral_eq, map_pow]`. Establish `E4 : ∀ i : Fin 2, at1 i (dz w) = 2 * at1 i (sW w) * at1 i (dz (sW w))`. Introduce `i`. Use `congrArg (at1 i) h4` as an intermediate fact.

Simplify `this.symm` using `only [Add1.triple_lintegral_eq, map_mul, map_ofNat]`. Establish `E5 : ∀ i : Fin 2, at1 i (dz (sW w)) ^ 2 = 1 + MvPowerSeries.C A * at1 i (sW w) ^ 2 + MvPowerSeries.C kap * (at1 i (sW w) ^ 2) ^ 2`. Introduce `i`. Use `congrArg (at1 i) h5` as an intermediate fact. Rewrite using `[← E1]`.

Simplify `this` using `only [Add1.triple_lintegral_eq, map_pow, map_add, map_mul, map_one, Add1.inVarAlgHom_C]`. Establish `E6 : ∀ i : Fin 2, at1 i (dz (dz (sW w))) = (MvPowerSeries.C A + 2 * MvPowerSeries.C kap * at1 i (sW w) ^ 2) * at1 i (sW w)`. Introduce `i`. Use `congrArg (at1 i) h6` as an intermediate fact. Rewrite using `[← E1]`.

Simplify `this` using `only [Add1.triple_lintegral_eq, map_add, map_mul, map_ofNat, Add1.inVarAlgHom_C]`. Use `set d : MvPowerSeries (Fin 2) K := 1 - MvPowerSeries.C kap * at1 0 w * at1 1 w with hd`. Use `set n : MvPowerSeries (Fin 2) K := at1 0 (sW w) * at1 1 (dz (sW w)) + at1 1 (sW w) * at1 0 (dz (sW w)) with hn`. Establish `hd0 : MvPowerSeries.constantCoeff d = 1`. Rewrite using `[hd, map_sub, map_mul, Add1.constantCoeff_inVar_eq_zero 1 hw0, mul_zero, map_one, sub_zero]`.

Establish `hdne : d ≠ 0`. Introduce `h`. Rewrite `hd0` using `[h, map_zero]`. Conclude with `zero_ne_one hd0`. Establish `hdi : d⁻¹ * d = 1` using `MvPowerSeries.inv_mul_cancel d (by rw [hd0]; exact one_ne_zero)`.

Establish `hhd : n * d⁻¹ * d = n` using `by rw [mul_assoc, hdi, mul_one]`. Establish `n01 : (1 : Fin 2) ≠ 0` using `by decide`. Establish `n10 : (0 : Fin 2) ≠ 1` using `by decide`. Establish `pn0 : pd 0 n = at1 1 (dz (sW w)) * at1 0 (dz (sW w)) + at1 1 (sW w) * at1 0 (dz (dz (sW w)))`. Rewrite using `[hn, pd, map_add]`.

Express the relevant statement in the definitionally equal form `pd 0 _ + pd 0 _ = _`. Rewrite using `[Add1.pd_mul, Add1.pd_mul, partialDeriv_inVar_self, partialDeriv_inVar_self, pderiv_at_variable_of_ne n01, pderiv_at_variable_of_ne n01]`. Expand and normalize the polynomial expressions, which then agree. Establish `pn1 : pd 1 n = at1 0 (sW w) * at1 1 (dz (dz (sW w))) + at1 0 (dz (sW w)) * at1 1 (dz (sW w))`. Rewrite using `[hn, pd, map_add]`.

Express the relevant statement in the definitionally equal form `pd 1 _ + pd 1 _ = _`. Rewrite using `[Add1.pd_mul, Add1.pd_mul, partialDeriv_inVar_self, partialDeriv_inVar_self, pderiv_at_variable_of_ne n10, pderiv_at_variable_of_ne n10]`. Expand and normalize the polynomial expressions, which then agree. Establish `pC : ∀ i : Fin 2, pd i (MvPowerSeries.C kap : MvPowerSeries (Fin 2) K) = 0` using `fun i => MvPowerSeries.pderiv_C`. Establish `p1 : ∀ i : Fin 2, pd i (1 : MvPowerSeries (Fin 2) K) = 0` using `fun i => MvPowerSeries.pderiv_one`.

Establish `pd0 : pd 0 d = -(MvPowerSeries.C kap * at1 0 (dz w) * at1 1 w)`. Rewrite using `[hd, Add1.pd_sub, Add1.pd_mul, Add1.pd_mul, p1, pC, partialDeriv_inVar_self, pderiv_at_variable_of_ne n01]`. Expand and normalize the polynomial expressions, which then agree. Establish `pd1 : pd 1 d = -(MvPowerSeries.C kap * at1 0 w * at1 1 (dz w))`. Rewrite using `[hd, Add1.pd_sub, Add1.pd_mul, Add1.pd_mul, p1, pC, partialDeriv_inVar_self, pderiv_at_variable_of_ne n10]`.

Expand and normalize the polynomial expressions, which then agree. Establish `halg : d * (pd 0 n - pd 1 n) = n * (pd 0 d - pd 1 d)`. Use `shear_alg (MvPowerSeries.C kap) (MvPowerSeries.C A) (at1 0 (sW w)) (at1 1 (sW w)) (at1 0 (dz (sW w))) (at1 1 (dz (sW w))) (E5 0) (E5 1)` as an intermediate fact. Rewrite using `[pn0, pn1, pd0, pd1, hd, hn, E6, E6, E4, E4, E1, E1]`. Take the linear combination `this`.

Establish `q0` using `congrArg (pd 0) hhd`. Establish `q1` using `congrArg (pd 1) hhd`. Rewrite `q0`, `q1` using `[Add1.pd_mul]`. Establish `hsh : pd 0 (n * d⁻¹) = pd 1 (n * d⁻¹)`. Use `sub_eq_zero.mp ?_` and prove the remaining obligations.

Use `(mul_eq_zero.mp (?_ : (d * d) * (pd 0 (n * d⁻¹) - pd 1 (n * d⁻¹)) = 0)).resolve_left (mul_ne_zero hdne hdne)` and prove the remaining obligations. Take the linear combination `d * q0 - d * q1 + halg - (pd 0 d - pd 1 d) * hhd`. Establish `hS` using `shear_two_variables_holds K (n * d⁻¹) hsh`. Establish `hev : ev0 (n * d⁻¹) = sW w`. Establish `e` using `congrArg ev0 hhd`.

Establish `ed : ev0 d = 1`. Rewrite using `[hd, eval_second_zero_sub, evalYZero_mul, restrictSecondZero_inVar_one, hw0, map_zero, mul_zero, eval_second_zero_one, sub_zero]`. Establish `en : ev0 n = sW w`. Rewrite using `[hn, evalYZero_add, evalYZero_mul, evalYZero_mul, eval_second_zero_at_variable_zero, restrictSecondZero_inVar_one, restrictSecondZero_inVar_one, h2, constantCoeff_dz_sW hw2, map_zero, map_one, mul_one, zero_mul, add_zero]`. Rewrite `e` using `[evalYZero_mul, ed, mul_one, en]`. Then use the resulting hypothesis.

Rewrite `hS` using `[hev]`. Rewrite using `[← hS, hhd]`.
-/
theorem sigma_addition_holds : SAdd := by
  intro K _ _ A kap w hw
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sigma_rules_hold K A kap w hw
  obtain ⟨hw0, hw2, -⟩ := hw
  have E1 : ∀ i : Fin 2, at1 i w = at1 i (sW w) ^ 2 := by
    intro i
    have := congrArg (at1 i) h1
    simpa only [Add1.triple_lintegral_eq, map_pow] using this.symm
  have E4 : ∀ i : Fin 2, at1 i (dz w) = 2 * at1 i (sW w) * at1 i (dz (sW w)) := by
    intro i
    have := congrArg (at1 i) h4
    simpa only [Add1.triple_lintegral_eq, map_mul, map_ofNat] using this.symm
  have E5 : ∀ i : Fin 2, at1 i (dz (sW w)) ^ 2 =
      1 + MvPowerSeries.C A * at1 i (sW w) ^ 2 + MvPowerSeries.C kap * (at1 i (sW w) ^ 2) ^ 2 := by
    intro i
    have := congrArg (at1 i) h5
    rw [← E1]
    simpa only [Add1.triple_lintegral_eq, map_pow, map_add, map_mul, map_one, Add1.inVarAlgHom_C] using this
  have E6 : ∀ i : Fin 2, at1 i (dz (dz (sW w))) =
      (MvPowerSeries.C A + 2 * MvPowerSeries.C kap * at1 i (sW w) ^ 2) * at1 i (sW w) := by
    intro i
    have := congrArg (at1 i) h6
    rw [← E1]
    simpa only [Add1.triple_lintegral_eq, map_add, map_mul, map_ofNat, Add1.inVarAlgHom_C] using this
  set d : MvPowerSeries (Fin 2) K := 1 - MvPowerSeries.C kap * at1 0 w * at1 1 w with hd
  set n : MvPowerSeries (Fin 2) K :=
    at1 0 (sW w) * at1 1 (dz (sW w)) + at1 1 (sW w) * at1 0 (dz (sW w)) with hn
  have hd0 : MvPowerSeries.constantCoeff d = 1 := by
    rw [hd, map_sub, map_mul, Add1.constantCoeff_inVar_eq_zero 1 hw0, mul_zero, map_one, sub_zero]
  have hdne : d ≠ 0 := by
    intro h
    rw [h, map_zero] at hd0
    exact zero_ne_one hd0
  have hdi : d⁻¹ * d = 1 := MvPowerSeries.inv_mul_cancel d (by rw [hd0]; exact one_ne_zero)
  have hhd : n * d⁻¹ * d = n := by rw [mul_assoc, hdi, mul_one]
  have n01 : (1 : Fin 2) ≠ 0 := by decide
  have n10 : (0 : Fin 2) ≠ 1 := by decide
  have pn0 : pd 0 n = at1 1 (dz (sW w)) * at1 0 (dz (sW w)) +
      at1 1 (sW w) * at1 0 (dz (dz (sW w))) := by
    rw [hn, pd, map_add]
    change pd 0 _ + pd 0 _ = _
    rw [Add1.pd_mul, Add1.pd_mul, partialDeriv_inVar_self, partialDeriv_inVar_self, pderiv_at_variable_of_ne n01, pderiv_at_variable_of_ne n01]
    ring
  have pn1 : pd 1 n = at1 0 (sW w) * at1 1 (dz (dz (sW w))) +
      at1 0 (dz (sW w)) * at1 1 (dz (sW w)) := by
    rw [hn, pd, map_add]
    change pd 1 _ + pd 1 _ = _
    rw [Add1.pd_mul, Add1.pd_mul, partialDeriv_inVar_self, partialDeriv_inVar_self, pderiv_at_variable_of_ne n10, pderiv_at_variable_of_ne n10]
    ring
  have pC : ∀ i : Fin 2, pd i (MvPowerSeries.C kap : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.pderiv_C
  have p1 : ∀ i : Fin 2, pd i (1 : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.pderiv_one
  have pd0 : pd 0 d = -(MvPowerSeries.C kap * at1 0 (dz w) * at1 1 w) := by
    rw [hd, Add1.pd_sub, Add1.pd_mul, Add1.pd_mul, p1, pC, partialDeriv_inVar_self, pderiv_at_variable_of_ne n01]
    ring
  have pd1 : pd 1 d = -(MvPowerSeries.C kap * at1 0 w * at1 1 (dz w)) := by
    rw [hd, Add1.pd_sub, Add1.pd_mul, Add1.pd_mul, p1, pC, partialDeriv_inVar_self, pderiv_at_variable_of_ne n10]
    ring
  have halg : d * (pd 0 n - pd 1 n) = n * (pd 0 d - pd 1 d) := by
    have := shear_alg (MvPowerSeries.C kap) (MvPowerSeries.C A) (at1 0 (sW w)) (at1 1 (sW w))
      (at1 0 (dz (sW w))) (at1 1 (dz (sW w))) (E5 0) (E5 1)
    rw [pn0, pn1, pd0, pd1, hd, hn, E6, E6, E4, E4, E1, E1]
    linear_combination this
  have q0 := congrArg (pd 0) hhd
  have q1 := congrArg (pd 1) hhd
  rw [Add1.pd_mul] at q0 q1
  have hsh : pd 0 (n * d⁻¹) = pd 1 (n * d⁻¹) := by
    refine sub_eq_zero.mp ?_
    refine (mul_eq_zero.mp (?_ : (d * d) * (pd 0 (n * d⁻¹) - pd 1 (n * d⁻¹)) = 0)).resolve_left
      (mul_ne_zero hdne hdne)
    linear_combination d * q0 - d * q1 + halg - (pd 0 d - pd 1 d) * hhd
  have hS := shear_two_variables_holds K (n * d⁻¹) hsh
  have hev : ev0 (n * d⁻¹) = sW w := by
    have e := congrArg ev0 hhd
    have ed : ev0 d = 1 := by
      rw [hd, eval_second_zero_sub, evalYZero_mul, restrictSecondZero_inVar_one, hw0, map_zero, mul_zero, eval_second_zero_one, sub_zero]
    have en : ev0 n = sW w := by
      rw [hn, evalYZero_add, evalYZero_mul, evalYZero_mul, eval_second_zero_at_variable_zero, restrictSecondZero_inVar_one, restrictSecondZero_inVar_one, h2,
        constantCoeff_dz_sW hw2, map_zero, map_one, mul_one, zero_mul, add_zero]
    rwa [evalYZero_mul, ed, mul_one, en] at e
  rw [hev] at hS
  rw [← hS, hhd]

/- English proof (translation)
Introduce `K _ _ A kap w hw`. Establish `H` using `sigma_addition_holds K A kap w hw`. Take `⟨h1, -, -, h4, -, -⟩` from `sigma_rules_hold K A kap w hw`. Establish `E1 : ∀ i : Fin 2, at1 i w = at1 i (sW w) ^ 2`. Introduce `i`.

Use `congrArg (at1 i) h1` as an intermediate fact. Simplify `this.symm` using `only [Add1.triple_lintegral_eq, map_pow]`. Establish `E4 : ∀ i : Fin 2, at1 i (dz w) = 2 * at1 i (sW w) * at1 i (dz (sW w))`. Introduce `i`. Use `congrArg (at1 i) h4` as an intermediate fact.

Simplify `this.symm` using `only [Add1.triple_lintegral_eq, map_mul, map_ofNat]`. Establish `ES : atS w = atS (sW w) ^ 2` using `by rw [← atS_sq, h1]`. Rewrite `H` using `[E1, E1]`. Rewrite using `[ES, E4, E4, E1, E1]`. Take the linear combination `(4 * at1 0 (sW w) ^ 2 * at1 1 (sW w) ^ 2 * (atS (sW w) * (1 - MvPowerSeries.C kap * at1 0 (sW w) ^ 2 * at1 1 (sW w) ^ 2) + (at1 0 (sW w) * at1 1 (dz (sW w)) + at1 1 (sW w) * at1 0 (dz (sW w))))) * H`.
-/
theorem weierstrass_addition_holds : WAdd := by
  intro K _ _ A kap w hw
  have H := sigma_addition_holds K A kap w hw
  obtain ⟨h1, -, -, h4, -, -⟩ := sigma_rules_hold K A kap w hw
  have E1 : ∀ i : Fin 2, at1 i w = at1 i (sW w) ^ 2 := by
    intro i
    have := congrArg (at1 i) h1
    simpa only [Add1.triple_lintegral_eq, map_pow] using this.symm
  have E4 : ∀ i : Fin 2, at1 i (dz w) = 2 * at1 i (sW w) * at1 i (dz (sW w)) := by
    intro i
    have := congrArg (at1 i) h4
    simpa only [Add1.triple_lintegral_eq, map_mul, map_ofNat] using this.symm
  have ES : atS w = atS (sW w) ^ 2 := by rw [← atS_sq, h1]
  rw [E1, E1] at H
  rw [ES, E4, E4, E1, E1]
  linear_combination (4 * at1 0 (sW w) ^ 2 * at1 1 (sW w) ^ 2 *
    (atS (sW w) * (1 - MvPowerSeries.C kap * at1 0 (sW w) ^ 2 * at1 1 (sW w) ^ 2) +
      (at1 0 (sW w) * at1 1 (dz (sW w)) + at1 1 (sW w) * at1 0 (dz (sW w))))) * H

end Formalism.L2.Th1.B.SAdd
