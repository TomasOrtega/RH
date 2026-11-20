import Formalism.LocalToGlobal.CharacterGerms.TripleMultiplicationConstantCoeff

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality Formalism.L2.FormalSeriesBounds.MulLFrob Formalism.L2.FormalSeriesBounds.LiftedCoordinateEvaluation
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C} {O : Type} [CommRing O] [StarRing O]

/- English proof (translation)
Establish `hu : Y.u1 = FB.expS C (evl Y V.l Y.h - (V.l : C) • Y.h)` using `rfl`. Establish `hE0 : constantCoeff (evl Y V.l Y.h - (V.l : C) • Y.h) = 0`. Rewrite using `[map_sub, show (V.l : C) • Y.h = ((V.l : ℕ) : PS C 2 dd) * Y.h by`. Rewrite using `[Nat.cast_smul_eq_nsmul, nsmul_eq_mul], map_mul, PartialDerivEval.h_const, mul_zero, sub_zero]`. Conclude with `FirstUnitSeriesIntegrality.height_multiple_constantCoeff Y V.l`.

Establish `hd : pderiv C ((0 : Fin 2), i) Y.u1 = (V.l : PS C 2 dd) * (Y.u1 * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i)`. Rewrite using `[hu, PartialDerivEval.pderiv_expS hE0, dE, ← hu]`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : IntS V (Y.u1 * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i)`. Use `PartialDerivEval.intS_mul (first_unit_series_integral C V O dd Y) (PartialDerivEval.intS_sum _ fun m _ => PartialDerivEval.intS_mul ?_ ?_)` and prove the remaining obligations.

Establish `hP : IntS V (Pm Y m)`. Use `PartialDerivEval.intS_ev constant_zero_lift_triple (fun k j => ?_) (PartialDerivEval.intS_pderiv Y.intPh1 _)` and prove the remaining obligations. Use `fin_cases k`. Conclude with `PartialDerivEval.intS_X _`. Conclude with `PartialDerivEval.intS_zero`.

Conclude with `PartialDerivEval.intS_X _`. Establish `hP' : IntS V (evl Y V.l (Pm Y m))`. Use `PartialDerivEval.intS_ev (constant_zero_double_multiplication Y V.l) (fun k j => ?_) hP` and prove the remaining obligations. Use `fin_cases k`. Conclude with `FirstUnitSeriesIntegrality.double_multiplication_integral Y.B.G Y.intF V.l j`.

Conclude with `PartialDerivEval.intS_X _`. Rewrite using `[sub_eq_add_neg]`. Conclude with `PartialDerivEval.intS_add hP (PartialDerivEval.intS_neg hP')`. Use `PartialDerivEval.intS_ev (PartialDerivEval.z0_1 _ z0P0) (fun k j => ?_) (MulLFrob.JL_int Y m i) fin_cases k` and prove the remaining obligations. Conclude with `PartialDerivEval.intS_X _`.

Rewrite using `[hd]`. Conclude with `MaximalIdealCongruence.mms_l_mul hint`.
-/
theorem pderiv_first_unit_series_maximal (Y : FBChart C V O dd) (i : Fin dd) : MaximalIdealCongruence.MMS V (pderiv C ((0 : Fin 2), i) Y.u1) := by
  have hu : Y.u1 = FB.expS C (evl Y V.l Y.h - (V.l : C) • Y.h) := rfl
  have hE0 : constantCoeff (evl Y V.l Y.h - (V.l : C) • Y.h) = 0 := by
    rw [map_sub, show (V.l : C) • Y.h = ((V.l : ℕ) : PS C 2 dd) * Y.h by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul], map_mul, PartialDerivEval.h_const, mul_zero, sub_zero]
    exact FirstUnitSeriesIntegrality.height_multiple_constantCoeff Y V.l
  have hd : pderiv C ((0 : Fin 2), i) Y.u1 =
      (V.l : PS C 2 dd) * (Y.u1 * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i) := by
    rw [hu, PartialDerivEval.pderiv_expS hE0, dE, ← hu]; ring
  have hint : IntS V (Y.u1 * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i) := by
    refine PartialDerivEval.intS_mul (first_unit_series_integral C V O dd Y)
      (PartialDerivEval.intS_sum _ fun m _ => PartialDerivEval.intS_mul ?_ ?_)
    · have hP : IntS V (Pm Y m) := by
        refine PartialDerivEval.intS_ev constant_zero_lift_triple (fun k j => ?_) (PartialDerivEval.intS_pderiv Y.intPh1 _)
        fin_cases k
        · exact PartialDerivEval.intS_X _
        · exact PartialDerivEval.intS_zero
        · exact PartialDerivEval.intS_X _
      have hP' : IntS V (evl Y V.l (Pm Y m)) := by
        refine PartialDerivEval.intS_ev (constant_zero_double_multiplication Y V.l) (fun k j => ?_) hP
        fin_cases k
        · exact FirstUnitSeriesIntegrality.double_multiplication_integral Y.B.G Y.intF V.l j
        · exact PartialDerivEval.intS_X _
      rw [sub_eq_add_neg]
      exact PartialDerivEval.intS_add hP (PartialDerivEval.intS_neg hP')
    · refine PartialDerivEval.intS_ev (PartialDerivEval.z0_1 _ z0P0) (fun k j => ?_) (MulLFrob.JL_int Y m i)
      fin_cases k
      exact PartialDerivEval.intS_X _
  rw [hd]; exact MaximalIdealCongruence.mms_l_mul hint

/- English proof (translation)
Introduce `k j` and use `by fin_cases k · exact hP j · exact hw j`.
-/
theorem int_two {w : Pt C 3 dd} (P : Pt C 3 dd) (hP : ∀ j, IntS V (P j)) (hw : ∀ j, IntS V (w j)) :
    ∀ k j, IntS V ((![P, w] : Fin 2 → Pt C 3 dd) k j) := fun k j => by
  fin_cases k
  · exact hP j
  · exact hw j

/- English proof (translation)
The claim follows from `intS_X _`.
-/
theorem triple_coordinate_integral (k : Fin 3) (j : Fin dd) : IntS V ((p3 k : Pt C 3 dd) j) := intS_X _

/- English proof (translation)
The claim follows from `intS_ev (constant_zero_two_points _ (z0p3 0) hw0) (int_two _ (triple_coordinate_integral 0) hw) (first_unit_series_integral C V O dd Y)`.
-/
theorem UU_int (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0)
    (hw : ∀ j, IntS V (w j)) : IntS V (UU Y w) :=
  intS_ev (constant_zero_two_points _ (z0p3 0) hw0) (int_two _ (triple_coordinate_integral 0) hw) (first_unit_series_integral C V O dd Y)

/- English proof (translation)
Introduce `i`. Unfold `UU`. Rewrite using `[d_ev_keep hw0 i (hd i)]`. Conclude with `MaximalIdealCongruence.MMS.ev_of (constant_zero_two_points _ (z0p3 0) hw0) (int_two _ (triple_coordinate_integral 0) hw) (pderiv_first_unit_series_maximal Y i)`.
-/
theorem UU_frob (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0)
    (hw : ∀ j, IntS V (w j)) (hd : ∀ i j, pderiv C ((0 : Fin 3), i) (w j) = 0) : FrobD V (UU Y w) := by
  intro i
  unfold UU
  rw [d_ev_keep hw0 i (hd i)]
  exact MaximalIdealCongruence.MMS.ev_of (constant_zero_two_points _ (z0p3 0) hw0) (int_two _ (triple_coordinate_integral 0) hw) (pderiv_first_unit_series_maximal Y i)

/- English proof (translation)
Establish `hz` using `constant_zero_two_points (p3 0) (z0p3 0) hw0`. Establish `hw' : ∀ j, constantCoeff (ev (rz (C` using `C) (dd := dd) 2) (w j)) = 0 := fun j => const_ev (constant_zero_restrict_points 2) (hw0 j)`. Establish `hE0 : constantCoeff (ev (n` using `3) ![m3 Y.B.G V.l, w] Y.h - (V.l : C) • ev (n := 3) ![p3 0, w] Y.h) = 0 := by`. Rewrite using `[map_sub, eval_height_constantCoeff Y (triple_multiplication_constantCoeff _ _) hw0, show (V.l : C) • ev (n := 3) ![p3 0, w] Y.h = MvPowerSeries.C (V.l : C) * ev (n := 3) ![p3 0, w] Y.h from MvPowerSeries.smul_eq_C_mul _ _, map_mul, eval_height_constantCoeff Y (z0p3 0) hw0, mul_z …`. Rewrite using `[UU_eq Y w hw0, ev_ex (constant_zero_restrict_points 2) _ hE0, ev_sub (constant_zero_restrict_points 2), ev_smulC (constant_zero_restrict_points 2), ev_ev (constant_zero_two_points _ (triple_multiplication_constantCoeff _ _) hw0) (constant_zero_restrict_points 2), ev_ev hz (const …`.

Establish `e1 : (fun k j => ev (rz (C` using `C) (dd := dd) 2) ((![m3 Y.B.G V.l, w] : Fin 2 → Pt C 3 dd) k j)) = ![0, fun j => ev (rz 2) (w j)] := by`. Use function extensionality and compare the values at `k j`. Use `fin_cases k`. Conclude with `restrict_triple_multiplication _ _ j`. Both sides reduce to the same expression.

Establish `e2 : (fun k j => ev (rz (C` using `C) (dd := dd) 2) ((![p3 0, w] : Fin 2 → Pt C 3 dd) k j)) = ![0, fun j => ev (rz 2) (w j)] := by`. Use function extensionality and compare the values at `k j`. Use `fin_cases k`. Conclude with `ev_X (constant_zero_restrict_points 2) 0 j`. Both sides reduce to the same expression.

Rewrite using `[e1, e2, height_at_zero_first Y _ hw', smul_zero, sub_zero, ex_zero]`.
-/
theorem UU_one (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0) :
    ev (rz 2) (UU Y w) = 1 := by
  have hz := constant_zero_two_points (p3 0) (z0p3 0) hw0
  have hw' : ∀ j, constantCoeff (ev (rz (C := C) (dd := dd) 2) (w j)) = 0 := fun j => const_ev (constant_zero_restrict_points 2) (hw0 j)
  have hE0 : constantCoeff (ev (n := 3) ![m3 Y.B.G V.l, w] Y.h - (V.l : C) • ev (n := 3) ![p3 0, w] Y.h) = 0 := by
    rw [map_sub, eval_height_constantCoeff Y (triple_multiplication_constantCoeff _ _) hw0, show (V.l : C) • ev (n := 3) ![p3 0, w] Y.h =
      MvPowerSeries.C (V.l : C) * ev (n := 3) ![p3 0, w] Y.h from MvPowerSeries.smul_eq_C_mul _ _, map_mul,
      eval_height_constantCoeff Y (z0p3 0) hw0, mul_zero, sub_zero]
  rw [UU_eq Y w hw0, ev_ex (constant_zero_restrict_points 2) _ hE0, ev_sub (constant_zero_restrict_points 2), ev_smulC (constant_zero_restrict_points 2),
    ev_ev (constant_zero_two_points _ (triple_multiplication_constantCoeff _ _) hw0) (constant_zero_restrict_points 2), ev_ev hz (constant_zero_restrict_points 2)]
  have e1 : (fun k j => ev (rz (C := C) (dd := dd) 2) ((![m3 Y.B.G V.l, w] : Fin 2 → Pt C 3 dd) k j)) =
      ![0, fun j => ev (rz 2) (w j)] := by
    funext k j; fin_cases k
    · exact restrict_triple_multiplication _ _ j
    · rfl
  have e2 : (fun k j => ev (rz (C := C) (dd := dd) 2) ((![p3 0, w] : Fin 2 → Pt C 3 dd) k j)) =
      ![0, fun j => ev (rz 2) (w j)] := by
    funext k j; fin_cases k
    · exact ev_X (constant_zero_restrict_points 2) 0 j
    · rfl
  rw [e1, e2, height_at_zero_first Y _ hw', smul_zero, sub_zero, ex_zero]

/- English proof (translation)
Introduce `k j` and use `by fin_cases k · exact triple_multiplication_constantCoeff _ _ j · exact z0p3 1 j · exact z0p3 2 j`.
-/
theorem constant_zero_triple_multiplication (Y : FBChart C V O dd) : Z0 (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) := fun k j => by
  fin_cases k
  · exact triple_multiplication_constantCoeff _ _ j
  · exact z0p3 1 j
  · exact z0p3 2 j

/- English proof (translation)
Use `intS_ev (constant_zero_triple_multiplication Y) (fun k j => ?_) Y.intPh2` and prove the remaining obligations. Use `fin_cases k`. Conclude with `triple_multiplication_integral _ Y.intF _ j`. Conclude with `intS_X _`. Conclude with `intS_X _`.
-/
theorem QQ_int (Y : FBChart C V O dd) : IntS V (QQ Y) := by
  refine intS_ev (constant_zero_triple_multiplication Y) (fun k j => ?_) Y.intPh2
  fin_cases k
  · exact triple_multiplication_integral _ Y.intF _ j
  · exact intS_X _
  · exact intS_X _

/- English proof (translation)
Use `show pderiv C ((0 : Fin 3), i) (ev ![(p3 0 : Pt C 3 dd)] (mulL Y.B.G.F V.l k)) = _`. Rewrite using `[pderiv_eval_single (P := (p3 0 : Pt C 3 dd)) (z0p3 0), Finset.sum_eq_single i (fun j _ hj => by show _ * pderiv C _ (pt C (n := 3) dd 0 j) = 0`. Rewrite using `[LiftedCoordinateEvaluation.pderiv_pt_same, if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]`. Use `show _ * pderiv C _ (pt C (n := 3) dd 0 i) = _`. Rewrite using `[LiftedCoordinateEvaluation.pderiv_pt_same, if_pos rfl, mul_one]`.

Both sides reduce to the same expression.
-/
theorem pderiv_triple_multiplication (Y : FBChart C V O dd) (k i : Fin dd) :
    pderiv C ((0 : Fin 3), i) (m3 Y.B.G V.l k) = ev ![(p3 0 : Pt C 3 dd)] (Jac (mulL Y.B.G.F V.l) k i) := by
  show pderiv C ((0 : Fin 3), i) (ev ![(p3 0 : Pt C 3 dd)] (mulL Y.B.G.F V.l k)) = _
  rw [pderiv_eval_single (P := (p3 0 : Pt C 3 dd)) (z0p3 0), Finset.sum_eq_single i (fun j _ hj => by
      show _ * pderiv C _ (pt C (n := 3) dd 0 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_same, if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]
  show _ * pderiv C _ (pt C (n := 3) dd 0 i) = _
  rw [LiftedCoordinateEvaluation.pderiv_pt_same, if_pos rfl, mul_one]
  rfl

/- English proof (translation)
Rewrite using `[pderiv_triple_multiplication, jac_l, Matrix.smul_apply, ev_eq_alg (z0_1 _ (z0p3 0)), map_nsmul, ← ev_eq_alg (z0_1 _ (z0p3 0)), nsmul_eq_mul]`. Use `MaximalIdealCongruence.mms_l_mul (intS_ev (z0_1 _ (z0p3 0)) (fun k' j => by fin_cases k'; exact intS_X _) ?_)` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `intS_sum _ fun j _ => intS_mul ?_ (JL_int Y j i)` and prove the remaining obligations. Use `intS_ev (z0_1 _ (multiplication_constantCoeff_zero Y.B.G V.l)) (fun k' j' => ?_) (JF_int Y k j)` and prove the remaining obligations.

Use `fin_cases k'`. Conclude with `mulL_int Y.B.G Y.intF V.l j'`.
-/
theorem pderiv_triple_multiplication_maximal (Y : FBChart C V O dd) (k i : Fin dd) : MaximalIdealCongruence.MMS V (pderiv C ((0 : Fin 3), i) (m3 Y.B.G V.l k)) := by
  rw [pderiv_triple_multiplication, jac_l, Matrix.smul_apply, ev_eq_alg (z0_1 _ (z0p3 0)), map_nsmul, ← ev_eq_alg (z0_1 _ (z0p3 0)),
    nsmul_eq_mul]
  refine MaximalIdealCongruence.mms_l_mul (intS_ev (z0_1 _ (z0p3 0)) (fun k' j => by fin_cases k'; exact intS_X _) ?_)
  rw [Matrix.mul_apply]
  refine intS_sum _ fun j _ => intS_mul ?_ (JL_int Y j i)
  refine intS_ev (z0_1 _ (multiplication_constantCoeff_zero Y.B.G V.l)) (fun k' j' => ?_) (JF_int Y k j)
  fin_cases k'
  exact mulL_int Y.B.G Y.intF V.l j'

/- English proof (translation)
Introduce `i`. Unfold `QQ`. Rewrite using `[pderiv_eval_triple (constant_zero_triple_multiplication Y)]`. Establish `h1 : ∑ j, ev ![m3 Y.B.G V.l, p3 1, p3 2] (pderiv C ((1 : Fin 3), j) Y.B.ph2) * pderiv C ((0 : Fin 3), i) ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) 1 j) = 0` using `Finset.sum_eq_zero fun j _ => by show _ * pderiv C _ (pt C (n := 3) dd 1 j) = 0`. Rewrite using `[LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (1 : Fin 3) ≠ 0), mul_zero]`.

Establish `h2 : ∑ j, ev ![m3 Y.B.G V.l, p3 1, p3 2] (pderiv C ((2 : Fin 3), j) Y.B.ph2) * pderiv C ((0 : Fin 3), i) ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) 2 j) = 0` using `Finset.sum_eq_zero fun j _ => by show _ * pderiv C _ (pt C (n := 3) dd 2 j) = 0`. Rewrite using `[LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (2 : Fin 3) ≠ 0), mul_zero]`. Rewrite using `[h1, h2, add_zero, add_zero]`. Use `MaximalIdealCongruence.mms_sum _ fun j _ => MaximalIdealCongruence.MMS.mul_left ?_ (pderiv_triple_multiplication_maximal Y j i)` and prove the remaining obligations. Use `intS_ev (constant_zero_triple_multiplication Y) (fun k m => ?_) (intS_pderiv Y.intPh2 _)` and prove the remaining obligations.

Use `fin_cases k`. Conclude with `triple_multiplication_integral _ Y.intF _ m`. Conclude with `intS_X _`. Conclude with `intS_X _`.
-/
theorem QQ_frob (Y : FBChart C V O dd) : FrobD V (QQ Y) := by
  intro i
  unfold QQ
  rw [pderiv_eval_triple (constant_zero_triple_multiplication Y)]
  have h1 : ∑ j, ev ![m3 Y.B.G V.l, p3 1, p3 2] (pderiv C ((1 : Fin 3), j) Y.B.ph2) *
      pderiv C ((0 : Fin 3), i) ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) 1 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      show _ * pderiv C _ (pt C (n := 3) dd 1 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (1 : Fin 3) ≠ 0), mul_zero]
  have h2 : ∑ j, ev ![m3 Y.B.G V.l, p3 1, p3 2] (pderiv C ((2 : Fin 3), j) Y.B.ph2) *
      pderiv C ((0 : Fin 3), i) ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) 2 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      show _ * pderiv C _ (pt C (n := 3) dd 2 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (2 : Fin 3) ≠ 0), mul_zero]
  rw [h1, h2, add_zero, add_zero]
  refine MaximalIdealCongruence.mms_sum _ fun j _ => MaximalIdealCongruence.MMS.mul_left ?_ (pderiv_triple_multiplication_maximal Y j i)
  refine intS_ev (constant_zero_triple_multiplication Y) (fun k m => ?_) (intS_pderiv Y.intPh2 _)
  fin_cases k
  · exact triple_multiplication_integral _ Y.intF _ m
  · exact intS_X _
  · exact intS_X _

/- English proof (translation)
Use function extensionality and compare the values at `k j`. Apply the tactic sequence `fin_cases k <;> rfl`.
-/
theorem rz_eq : (rz (C := C) (dd := dd) 2) = ![0, pt C (n := 2) dd 0, pt C dd 1] := by
  funext k j
  fin_cases k <;> rfl

/- English proof (translation)
Unfold `QQ`. Rewrite using `[ev_ev (constant_zero_triple_multiplication Y) (constant_zero_restrict_points 2)]`. Establish `e : (fun k j => ev (rz (C` using `C) (dd := dd) 2) ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) k j)) = ![0, pt C (n := 2) dd 0, pt C dd 1] := by`. Use function extensionality and compare the values at `k j`. Use `fin_cases k`.

Conclude with `restrict_triple_multiplication _ _ j`. Conclude with `ev_X (constant_zero_restrict_points 2) 1 j`. Conclude with `ev_X (constant_zero_restrict_points 2) 2 j`. Rewrite using `[e]`. Conclude with `Y.B.cocycleRight_zero_fst`.
-/
theorem QQ_one (Y : FBChart C V O dd) : ev (rz 2) (QQ Y) = 1 := by
  unfold QQ
  rw [ev_ev (constant_zero_triple_multiplication Y) (constant_zero_restrict_points 2)]
  have e : (fun k j => ev (rz (C := C) (dd := dd) 2)
      ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) k j)) = ![0, pt C (n := 2) dd 0, pt C dd 1] := by
    funext k j; fin_cases k
    · exact restrict_triple_multiplication _ _ j
    · exact ev_X (constant_zero_restrict_points 2) 1 j
    · exact ev_X (constant_zero_restrict_points 2) 2 j
  rw [e]
  exact Y.B.cocycleRight_zero_fst

/- English proof (translation)
Rewrite using `[rz_eq]`. Conclude with `Y.B.cocycleRight_zero_fst`.
-/
theorem second_pairing_restrict_one (Y : FBChart C V O dd) : ev (rz 2) Y.B.ph2 = 1 := by
  rw [rz_eq]; exact Y.B.cocycleRight_zero_fst

/- English proof (translation)
Rewrite using `[ev_eq_alg (constant_zero_restrict_points 2), map_pow, ← ev_eq_alg (constant_zero_restrict_points 2), second_pairing_restrict_one, one_pow]`.
-/
theorem second_pairing_pow_restrict_one (Y : FBChart C V O dd) : ev (rz 2) (Y.B.ph2 ^ V.l) = 1 := by
  rw [ev_eq_alg (constant_zero_restrict_points 2), map_pow, ← ev_eq_alg (constant_zero_restrict_points 2), second_pairing_restrict_one, one_pow]

/- English proof (translation)
Introduce `i`. Rewrite using `[Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]`. Conclude with `MaximalIdealCongruence.mms_l_mul (intS_mul (intS_pow Y.intPh2 _) (intS_pderiv Y.intPh2 _))`.
-/
theorem second_pairing_pow_frobenius (Y : FBChart C V O dd) : FrobD V (Y.B.ph2 ^ V.l) := by
  intro i
  rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  exact MaximalIdealCongruence.mms_l_mul (intS_mul (intS_pow Y.intPh2 _) (intS_pderiv Y.intPh2 _))

end Formalism.L2.FormalSeriesBounds.FunEq
