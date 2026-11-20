import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalD
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementE

noncomputable section

namespace Formalism.L2.Th1.B.GCob

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)

section One

open PowerSeries

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Unfold `wOf`. Rewrite using `[mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]`.
-/
theorem wOf_mul (e1 : K) (P : PowerSeries K) :
    wOf e1 P * (1 + X ^ 2 * P - C e1 * X ^ 2) = X ^ 2 := by
  unfold wOf
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]

/- English proof (translation)
Establish `h1` using `wOf_mul e1 P`. Establish `e2 : dz ((X : PowerSeries K) ^ 2) = 2 * X`. Use `dz_X_pow (K := K) 1` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this`.

Establish `hd` using `congrArg dz h1`. Simplify using `only [dz_sub, dz_add, dz_mul, dz_one, dz_C, e2] at hd`. Take the linear combination `(1 + X ^ 2 * P - C e1 * X ^ 2) * hd - (X ^ 2 * dz P + P * (2 * X) - C e1 * (2 * X)) * h1`.
-/
theorem dz_wOf (e1 : K) (P : PowerSeries K) :
    (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * dz (wOf e1 P) = -(X * (-2 + X ^ 3 * dz P)) := by
  have h1 := wOf_mul e1 P
  have e2 : dz ((X : PowerSeries K) ^ 2) = 2 * X := by
    have := dz_X_pow (K := K) 1; push_cast at this; linear_combination this
  have hd := congrArg dz h1
  simp only [dz_sub, dz_add, dz_mul, dz_one, dz_C, e2] at hd
  linear_combination (1 + X ^ 2 * P - C e1 * X ^ 2) * hd -
    (X ^ 2 * dz P + P * (2 * X) - C e1 * (2 * X)) * h1

/- English proof (translation)
Establish `hs : HasSubst l` using `HasSubst.of_constantCoeff_zero' hl`. Use `congrArg (subst l) (wOf_mul e1 P)` as an intermediate fact. Rewrite `this` using `[← coe_substAlgHom hs]`. Simplify using `only [map_sub, map_mul, map_add, map_one, map_pow] at this`. Rewrite `this` using `[coe_substAlgHom hs, subst_X hs, subst_C]`.

Conclude with `this`.
-/
theorem subst_wOf_mul (e1 : K) (P : PowerSeries K) {l : PowerSeries K}
    (hl : constantCoeff l = 0) :
    subst l (wOf e1 P) * (1 + l ^ 2 * subst l P - C e1 * l ^ 2) = l ^ 2 := by
  have hs : HasSubst l := HasSubst.of_constantCoeff_zero' hl
  have := congrArg (subst l) (wOf_mul e1 P)
  rw [← coe_substAlgHom hs] at this
  simp only [map_sub, map_mul, map_add, map_one, map_pow] at this
  rw [coe_substAlgHom hs, subst_X hs, subst_C] at this
  exact this

/- English proof (translation)
Establish `hs : HasSubst l` using `HasSubst.of_constantCoeff_zero' hl`. Use `congrArg (subst l) (dz_wOf e1 P)` as an intermediate fact. Rewrite `this` using `[← coe_substAlgHom hs]`. Simplify using `only [map_sub, map_mul, map_add, map_one, map_pow, map_neg, map_ofNat] at this`. Rewrite `this` using `[coe_substAlgHom hs, subst_X hs, subst_C]`.

Conclude with `this`.
-/
theorem subst_dz_wOf (e1 : K) (P : PowerSeries K) {l : PowerSeries K}
    (hl : constantCoeff l = 0) :
    (1 + l ^ 2 * subst l P - C e1 * l ^ 2) ^ 2 * subst l (dz (wOf e1 P)) =
      -(l * (-2 + l ^ 3 * subst l (dz P))) := by
  have hs : HasSubst l := HasSubst.of_constantCoeff_zero' hl
  have := congrArg (subst l) (dz_wOf e1 P)
  rw [← coe_substAlgHom hs] at this
  simp only [map_sub, map_mul, map_add, map_one, map_pow, map_neg, map_ofNat] at this
  rw [coe_substAlgHom hs, subst_X hs, subst_C] at this
  exact this

/- English proof (translation)
Apply `mul_right_cancel₀ (pow_ne_zero 2 hl0)` to reduce the goal to its premises. Unfold `gT`. Establish `hw'` using `subst_wOf_mul (xT + c0) P hl`. Rewrite `hw'` using `[map_add]`. Take the linear combination `X ^ 2 * hw' - subst l (wOf (xT + c0) P) * hcv`.
-/
theorem wl_mul_g {c0 xT : K} {P l ep : PowerSeries K} (hl : constantCoeff l = 0) (hl0 : l ≠ 0)
    (hcv : X ^ 2 * (1 + l ^ 2 * subst l P) = l ^ 2 * (ep + C c0 * X ^ 2)) :
    subst l (wOf (xT + c0) P) * gT ep xT = X ^ 2 := by
  apply mul_right_cancel₀ (pow_ne_zero 2 hl0)
  unfold gT
  have hw' := subst_wOf_mul (xT + c0) P hl
  rw [map_add] at hw'
  linear_combination X ^ 2 * hw' - subst l (wOf (xT + c0) P) * hcv

/- English proof (translation)
Simplify using `[gT, hep]`.
-/
theorem constantCoeff_gT {ep : PowerSeries K} (xT : K) (hep : constantCoeff ep = 1) :
    constantCoeff (gT ep xT) = 1 := by
  simp [gT, hep]

/- English proof (translation)
Unfold `thT`. Rewrite using `[mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [constantCoeff_gT xT hep]; exact one_ne_zero), mul_one]`.
-/
theorem thT_mul {ep : PowerSeries K} (xT yT : K) (hep : constantCoeff ep = 1) :
    thT ep xT yT * gT ep xT = ep + C yT * X ^ 3 := by
  unfold thT
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [constantCoeff_gT xT hep]; exact one_ne_zero),
    mul_one]

/- English proof (translation)
Establish `hWg` using `wl_mul_g (xT := xT) hl hl0 hcv`. Establish `hth` using `thT_mul xT yT hep`. Establish `hZ` using `subst_dz_wOf (xT + c0) P hl`. Establish `hg0 : gT ep xT ≠ 0` using `ne_zero_of_constantCoeff (by rw [constantCoeff_gT xT hep]; exact one_ne_zero)`. Establish `hT' : 2 * (C yT : PowerSeries K) + C a1 * C xT + C a3 = 0`.

Simplify using `only [← map_ofNat (C (R := K)), ← map_mul, ← map_add]`. Rewrite using `[hT, map_zero]`. Rewrite `hZ` using `[map_add]`. Generalize the expression as in `subst l (dz (wOf (xT + c0) P)) = W' at hZ ⊢`. Generalize the expression as in `subst l (wOf (xT + c0) P) = W at hWg ⊢`.

Generalize the expression as in `subst l (dz P) = B at hZ h3`. Generalize the expression as in `subst l P = A at hZ hcv`. Generalize the expression as in `thT ep xT yT = th at hth ⊢`. Establish `hXZ : X ^ 2 * (1 + l ^ 2 * A - (C xT + C c0) * l ^ 2) = l ^ 2 * gT ep xT`. Unfold `gT`.

Take the linear combination `hcv`. Establish `hXZ2 : (X ^ 2 * (1 + l ^ 2 * A - (C xT + C c0) * l ^ 2)) ^ 2 = (l ^ 2 * gT ep xT) ^ 2`. Rewrite using `[hXZ]`. Establish `step1 : W' * gT ep xT ^ 2 = X * (2 * ep - C a1 * X * ep - C a3 * X ^ 3)`. Apply `mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 4 hl0) (pow_ne_zero 3 (PowerSeries.X_ne_zero (R := K))))` to reduce the goal to its premises.

Take the linear combination `-X ^ 3 * W' * hXZ2 + X ^ 7 * hZ - X ^ 4 * l * h3`. Apply `mul_left_cancel₀ (pow_ne_zero 2 hg0)` to reduce the goal to its premises. Simplify using `only [gT] at hWg hth step1 ⊢`. Take the linear combination `X * step1 - (2 * th * (ep - C xT * X ^ 2) - C a1 * X * (ep - C xT * X ^ 2)) * hWg - 2 * X ^ 2 * hth - X ^ 5 * hT'`.
-/
theorem wprime_core {c0 a1 a3 xT yT : K} {P l ep : PowerSeries K} (hl : constantCoeff l = 0)
    (hl0 : l ≠ 0) (hep : constantCoeff ep = 1)
    (hcv : X ^ 2 * (1 + l ^ 2 * subst l P) = l ^ 2 * (ep + C c0 * X ^ 2))
    (h3 : X ^ 3 * (-2 + l ^ 3 * subst l (dz P)) =
      l ^ 3 * (-2 * ep + C a1 * X * ep + C a3 * X ^ 3))
    (hT : 2 * yT + a1 * xT + a3 = 0) :
    X * subst l (dz (wOf (xT + c0) P)) =
      subst l (wOf (xT + c0) P) * (2 * thT ep xT yT - C a1 * X) := by
  have hWg := wl_mul_g (xT := xT) hl hl0 hcv
  have hth := thT_mul xT yT hep
  have hZ := subst_dz_wOf (xT + c0) P hl
  have hg0 : gT ep xT ≠ 0 :=
    ne_zero_of_constantCoeff (by rw [constantCoeff_gT xT hep]; exact one_ne_zero)
  have hT' : 2 * (C yT : PowerSeries K) + C a1 * C xT + C a3 = 0 := by
    simp only [← map_ofNat (C (R := K)), ← map_mul, ← map_add]; rw [hT, map_zero]
  rw [map_add] at hZ
  generalize subst l (dz (wOf (xT + c0) P)) = W' at hZ ⊢
  generalize subst l (wOf (xT + c0) P) = W at hWg ⊢
  generalize subst l (dz P) = B at hZ h3
  generalize subst l P = A at hZ hcv
  generalize thT ep xT yT = th at hth ⊢
  have hXZ : X ^ 2 * (1 + l ^ 2 * A - (C xT + C c0) * l ^ 2) = l ^ 2 * gT ep xT := by
    unfold gT; linear_combination hcv
  have hXZ2 : (X ^ 2 * (1 + l ^ 2 * A - (C xT + C c0) * l ^ 2)) ^ 2 = (l ^ 2 * gT ep xT) ^ 2 := by
    rw [hXZ]
  have step1 : W' * gT ep xT ^ 2 = X * (2 * ep - C a1 * X * ep - C a3 * X ^ 3) := by
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 4 hl0) (pow_ne_zero 3 (PowerSeries.X_ne_zero (R := K))))
    linear_combination -X ^ 3 * W' * hXZ2 + X ^ 7 * hZ - X ^ 4 * l * h3
  apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
  simp only [gT] at hWg hth step1 ⊢
  linear_combination X * step1 -
    (2 * th * (ep - C xT * X ^ 2) - C a1 * X * (ep - C xT * X ^ 2)) * hWg - 2 * X ^ 2 * hth -
    X ^ 5 * hT'

end One

/- English proof (translation)
Introduce `h`. Use `hL.2.2.2.1` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`.
-/
theorem ne_zero_of_law {K : Type} [NormedField K] {F : MvPowerSeries (Fin 2) K}
    {l : PowerSeries K} (hL : LawLog F l) : l ≠ 0 := by
  intro h
  have := hL.2.2.2.1
  rw [h] at this
  simp at this

/- English proof (translation)
Introduce `K _ _ _ g2 g3 c0 a1 a3 xT yT P l i ep F _ hL hC hC3 hT`. Conclude with `wprime_core hL.2.2.1 (ne_zero_of_law hL) hC.2.1 hC.2.2.1 hC3.1 hT`.
-/
theorem weierstrass_derivative_unit_holds : WPrimeU := by
  intro K _ _ _ g2 g3 c0 a1 a3 xT yT P l i ep F _ hL hC hC3 hT
  exact wprime_core hL.2.2.1 (ne_zero_of_law hL) hC.2.1 hC.2.2.1 hC3.1 hT

section Two

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst U` using `PowerSeries.HasSubst.of_constantCoeff_zero hU`. Use `congrArg (PowerSeries.subst U) h` as an intermediate fact. Rewrite `this` using `[PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs]`. Then use the resulting hypothesis.
-/
theorem subst_wg {ι : Type} {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0)
    {W g : PowerSeries K} (h : W * g = PowerSeries.X ^ 2) :
    PowerSeries.subst U W * PowerSeries.subst U g = U ^ 2 := by
  have hs : PowerSeries.HasSubst U := PowerSeries.HasSubst.of_constantCoeff_zero hU
  have := congrArg (PowerSeries.subst U) h
  rwa [PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs] at this

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K)` using `PowerSeries.HasSubst.X x`. Use `congrArg (PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries ι K)) h` as an intermediate fact. Rewrite `this` using `[← PowerSeries.coe_substAlgHom hs]`. Simplify using `only [map_sub, map_mul, map_ofNat] at this`. Rewrite `this` using `[PowerSeries.coe_substAlgHom hs, PowerSeries.subst_X hs, PowerSeries.subst_C]`.

Conclude with `this`.
-/
theorem at_variable_weierstrass_derivative {ι : Type} (x : ι) {W W' th : PowerSeries K} {a1 : K}
    (h : PowerSeries.X * W' = W * (2 * th - PowerSeries.C a1 * PowerSeries.X)) :
    MvPowerSeries.X x * at1 x W' =
      at1 x W * (2 * at1 x th - MvPowerSeries.C a1 * MvPowerSeries.X x) := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) := PowerSeries.HasSubst.X x
  have := congrArg (PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries ι K)) h
  rw [← PowerSeries.coe_substAlgHom hs] at this
  simp only [map_sub, map_mul, map_ofNat] at this
  rw [PowerSeries.coe_substAlgHom hs, PowerSeries.subst_X hs, PowerSeries.subst_C] at this
  exact this

/- English proof (translation)
Establish `h0 : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) l) = 0` using `PowerSeries.constantCoeff_subst_eq_zero (by simp) l hl`. Establish `h1 : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) l) = 0` using `PowerSeries.constantCoeff_subst_eq_zero (by simp) l hl`. Conclude with `Formalism.G.LogP.hs2 h0 h1`.
-/
theorem hsL {l : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0) :
    MvPowerSeries.HasSubst (![at1 (0 : Fin 2) l, at1 1 l] : Fin 2 → MvPowerSeries (Fin 2) K) := by
  have h0 : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by simp) l hl
  have h1 : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by simp) l hl
  exact Formalism.G.LogP.hs2 h0 h1

/- English proof (translation)
Introduce `h`. Establish `h2` using `congrArg (MvPowerSeries.pderiv K j) h`. Rewrite `h2` using `[MvPowerSeries.pderiv_X_self, map_zero]`. Conclude with `one_ne_zero h2`.
-/
theorem X_ne {ι : Type} (j : ι) : (MvPowerSeries.X j : MvPowerSeries ι K) ≠ 0 := by
  intro h
  have h2 := congrArg (MvPowerSeries.pderiv K j) h
  rw [MvPowerSeries.pderiv_X_self, map_zero] at h2
  exact one_ne_zero h2

/- English proof (translation)
Introduce `h`. Use `congrArg MvPowerSeries.constantCoeff h` as an intermediate fact. Rewrite `this` using `[map_ofNat, map_zero]`. Conclude with `absurd this (by norm_num)`.
-/
theorem four_ne {ι : Type} : (4 : MvPowerSeries ι K) ≠ 0 := by
  intro h
  have := congrArg MvPowerSeries.constantCoeff h
  rw [map_ofNat, map_zero] at this
  exact absurd this (by norm_num)

/- English proof (translation)
Rewrite using `[subst_at_variable_eq_subst f x (hsL hl), ParE.subst_inVar x f hl]`. Apply the tactic sequence `fin_cases x <;> rfl`.
-/
theorem subst_log_at_variable (f : PowerSeries K) (x : Fin 2) {l : PowerSeries K}
    (hl : PowerSeries.constantCoeff l = 0) :
    MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 1 l] (at1 x f) =
      at1 x (PowerSeries.subst l f) := by
  rw [subst_at_variable_eq_subst f x (hsL hl), ParE.subst_inVar x f hl]
  fin_cases x <;> rfl

/- English proof (translation)
Rewrite using `[ParO.subst_atS f (hsL hl), PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl) (PowerSeries.HasSubst.of_constantCoeff_zero hF), hFl]`. Both sides reduce to the same expression.
-/
theorem sub_atS (f : PowerSeries K) {l : PowerSeries K} {F : MvPowerSeries (Fin 2) K}
    (hl : PowerSeries.constantCoeff l = 0) (hF : MvPowerSeries.constantCoeff F = 0)
    (hFl : PowerSeries.subst F l = at1 0 l + at1 1 l) :
    MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 1 l] (atS f) =
      PowerSeries.subst F (PowerSeries.subst l f) := by
  rw [ParO.subst_atS f (hsL hl), PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hl) (PowerSeries.HasSubst.of_constantCoeff_zero hF),
    hFl]
  rfl

/- English proof (translation)
Establish `hb` using `hsL hl`. Establish `e` using `congrArg (MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 1 l]) h`. Rewrite `e` using `[← MvPowerSeries.coe_substAlgHom hb]`. Simplify using `only [map_sub, map_mul, map_one, map_pow, map_add, map_ofNat] at e`. Rewrite `e` using `[MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_C]`.

Simplify using `only [subst_log_at_variable _ _ hl, sub_atS _ hl hF hFl] at e`. Conclude with `e`.
-/
theorem wadd_law {kap : K} {w l : PowerSeries K} {F : MvPowerSeries (Fin 2) K}
    (hl : PowerSeries.constantCoeff l = 0) (hF : MvPowerSeries.constantCoeff F = 0)
    (hFl : PowerSeries.subst F l = at1 0 l + at1 1 l)
    (h : 4 * at1 0 w * at1 1 w * (1 - MvPowerSeries.C kap * at1 0 w * at1 1 w) ^ 2 * atS w =
      (at1 0 w * at1 1 (dz w) + at1 1 w * at1 0 (dz w)) ^ 2) :
    4 * at1 0 (PowerSeries.subst l w) * at1 1 (PowerSeries.subst l w) *
        (1 - MvPowerSeries.C kap * at1 0 (PowerSeries.subst l w) *
          at1 1 (PowerSeries.subst l w)) ^ 2 * PowerSeries.subst F (PowerSeries.subst l w) =
      (at1 0 (PowerSeries.subst l w) * at1 1 (PowerSeries.subst l (dz w)) +
        at1 1 (PowerSeries.subst l w) * at1 0 (PowerSeries.subst l (dz w))) ^ 2 := by
  have hb := hsL hl
  have e := congrArg (MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 1 l]) h
  rw [← MvPowerSeries.coe_substAlgHom hb] at e
  simp only [map_sub, map_mul, map_one, map_pow, map_add, map_ofNat] at e
  rw [MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_C] at e
  simp only [subst_log_at_variable _ _ hl, sub_atS _ hl hF hFl] at e
  exact e

/- English proof (translation)
Establish `hWa : Wa ≠ 0`. Introduce and unpack `rfl`. Rewrite `Ga` using `[zero_mul]`. Conclude with `pow_ne_zero 2 ha Ga.symm`. Establish `hWb : Wb ≠ 0`.

Introduce and unpack `rfl`. Rewrite `Gb` using `[zero_mul]`. Conclude with `pow_ne_zero 2 hb Gb.symm`. Establish `H : a * b * (Wa * Vb + Wb * Va) = 2 * Wa * Wb * (b * ta + a * tb - c * a * b)`. Take the linear combination `Wa * a * Hb + Wb * b * Ha`.

Establish `H2 : (a * b * (Wa * Vb + Wb * Va)) ^ 2 = (2 * Wa * Wb * (b * ta + a * tb - c * a * b)) ^ 2` using `by rw [H]`. Establish `h4 : (4 : R) * Wa ^ 2 * Wb ^ 2 ≠ 0` using `mul_ne_zero (mul_ne_zero h4' (pow_ne_zero 2 hWa)) (pow_ne_zero 2 hWb)`. Apply `mul_left_cancel₀ h4` to reduce the goal to its premises. Take the linear combination `-gF * H2 - gF * a ^ 2 * b ^ 2 * E1 + 4 * a ^ 2 * b ^ 2 * Wa * Wb * d ^ 2 * GF - 4 * Wa * Wb * Fv ^ 2 * d ^ 2 * (Wb * gb * Ga + a ^ 2 * Gb)`.
-/
theorem alg_core {R : Type} [CommRing R] [NoZeroDivisors R] (h4' : (4 : R) ≠ 0)
    {a b c Wa Wb Va Vb ta tb ga gb WF gF Fv d : R}
    (E1 : 4 * Wa * Wb * d ^ 2 * WF = (Wa * Vb + Wb * Va) ^ 2)
    (Ha : a * Va = Wa * (2 * ta - c * a)) (Hb : b * Vb = Wb * (2 * tb - c * b))
    (Ga : Wa * ga = a ^ 2) (Gb : Wb * gb = b ^ 2) (GF : WF * gF = Fv ^ 2)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    gF * (b * ta + a * tb - c * a * b) ^ 2 = ga * gb * Fv ^ 2 * d ^ 2 := by
  have hWa : Wa ≠ 0 := by
    rintro rfl
    rw [zero_mul] at Ga
    exact pow_ne_zero 2 ha Ga.symm
  have hWb : Wb ≠ 0 := by
    rintro rfl
    rw [zero_mul] at Gb
    exact pow_ne_zero 2 hb Gb.symm
  have H : a * b * (Wa * Vb + Wb * Va) = 2 * Wa * Wb * (b * ta + a * tb - c * a * b) := by
    linear_combination Wa * a * Hb + Wb * b * Ha
  have H2 : (a * b * (Wa * Vb + Wb * Va)) ^ 2 =
      (2 * Wa * Wb * (b * ta + a * tb - c * a * b)) ^ 2 := by rw [H]
  have h4 : (4 : R) * Wa ^ 2 * Wb ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h4' (pow_ne_zero 2 hWa)) (pow_ne_zero 2 hWb)
  apply mul_left_cancel₀ h4
  linear_combination -gF * H2 - gF * a ^ 2 * b ^ 2 * E1 + 4 * a ^ 2 * b ^ 2 * Wa * Wb * d ^ 2 * GF -
    4 * Wa * Wb * Fv ^ 2 * d ^ 2 * (Wb * gb * Ga + a ^ 2 * Gb)

end Two

/- English proof (translation)
Introduce `K _ _ _ g2 g3 c0 a1 a3 xT yT P l i ep F hWp hL hC hC3 hT he`. Establish `hl` using `hL.2.2.1`. Establish `hIW` using `wOfWp K g2 g3 (xT + c0) P hWp he`. Establish `E1` using `wadd_law hl hL.1 (ParO.log_law hL) (hW K _ _ _ hIW)`. Establish `hp` using `hP K g2 g3 c0 a1 a3 xT yT P l i ep F hWp hL hC hC3 hT`.

Establish `hg` using `wl_mul_g (xT := xT) hl (ne_zero_of_law hL) hC.2.2.1`. Unfold `LT`. Conclude with `alg_core four_ne E1 (at_variable_weierstrass_derivative 0 hp) (at_variable_weierstrass_derivative 1 hp) (subst_wg (MvPowerSeries.constantCoeff_X (0 : Fin 2)) hg) (subst_wg (MvPowerSeries.constantCoeff_X (1 : Fin 2)) hg) (subst_wg hL.1 hg) (X_ne 0) (X_ne 1)`.
-/
theorem GCob_of (hW : WAdd) (hP : WPrimeU) : GCob := by
  intro K _ _ _ g2 g3 c0 a1 a3 xT yT P l i ep F hWp hL hC hC3 hT he
  have hl := hL.2.2.1
  have hIW := wOfWp K g2 g3 (xT + c0) P hWp he
  have E1 := wadd_law hl hL.1 (ParO.log_law hL) (hW K _ _ _ hIW)
  have hp := hP K g2 g3 c0 a1 a3 xT yT P l i ep F hWp hL hC hC3 hT
  have hg := wl_mul_g (xT := xT) hl (ne_zero_of_law hL) hC.2.2.1
  unfold LT
  exact alg_core four_ne E1 (at_variable_weierstrass_derivative 0 hp) (at_variable_weierstrass_derivative 1 hp)
    (subst_wg (MvPowerSeries.constantCoeff_X (0 : Fin 2)) hg)
    (subst_wg (MvPowerSeries.constantCoeff_X (1 : Fin 2)) hg) (subst_wg hL.1 hg)
    (X_ne 0) (X_ne 1)

/- English proof (translation)
The claim follows from `GCob_of hW weierstrass_derivative_unit_holds`.
-/
theorem GCob_of' (hW : WAdd) : GCob := GCob_of hW weierstrass_derivative_unit_holds

end Formalism.L2.Th1.B.GCob
