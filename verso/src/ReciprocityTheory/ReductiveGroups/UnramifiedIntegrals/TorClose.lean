import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorChord

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

/- English proof (translation)
Rewrite using `[sub_eq_add_neg A B]`. Break down `A with _ | ⟨xA, yA, hA'⟩` into its components or cases. Conclude with `absurd rfl hA`. Break down `B with _ | ⟨xB, yB, hB'⟩` into its components or cases. Conclude with `absurd rfl hB`.

Distinguish the cases in `hx : xA = xB`. It suffices to derive a contradiction. Substitute `hx` using the available equality. Establish `e1` using `(WeierstrassCurve.Affine.equation_iff _ _).1 hA'.1`. Establish `e2` using `(WeierstrassCurve.Affine.equation_iff _ _).1 hB'.1`.

Establish `hm : (yA - yB) * (yA + yB) = 0`. Take the linear combination `e1 - e2 - xA * (yA - yB) * h1 - (yA - yB) * h3`. Break down `mul_eq_zero.1 hm with h | h` into its components or cases. Establish `hy : yA = yB` using `sub_eq_zero.1 h`. Substitute `hy` using the available equality.

Conclude with `hd (sub_self _)`. Establish `hy : yA = W.toAffine.negY xA yB`. Rewrite using `[WeierstrassCurve.Affine.negY]`. Take the linear combination `h + xA * h1 + h3`. Conclude with `hs (WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hy)`.

Establish `hx' : xA - xB ≠ 0` using `sub_ne_zero.2 hx`. Rewrite using `[WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.add_of_X_ne hx, WeierstrassCurve.Affine.Point.add_of_X_ne hx]`. Simplify using `only [px, py, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope_of_X_ne hx, WeierstrassCurve.Affine.negY, h1, h2, h3]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chord_identity {C : Type} [Field C] (W : WeierstrassCurve C) (h1 : W.a₁ = 0) (h2 : W.a₂ = 0)
    (h3 : W.a₃ = 0) (A B : W.toAffine.Point) (hA : A ≠ 0) (hB : B ≠ 0) (hs : A + B ≠ 0)
    (hd : A - B ≠ 0) :
    (px W A - px W B) ^ 2 * (px W (A + B) - px W (A - B)) = -4 * py W A * py W B := by
  rw [sub_eq_add_neg A B]
  rcases A with _ | ⟨xA, yA, hA'⟩
  · exact absurd rfl hA
  rcases B with _ | ⟨xB, yB, hB'⟩
  · exact absurd rfl hB
  by_cases hx : xA = xB
  · exfalso
    subst hx
    have e1 := (WeierstrassCurve.Affine.equation_iff _ _).1 hA'.1
    have e2 := (WeierstrassCurve.Affine.equation_iff _ _).1 hB'.1
    have hm : (yA - yB) * (yA + yB) = 0 := by
      linear_combination e1 - e2 - xA * (yA - yB) * h1 - (yA - yB) * h3
    rcases mul_eq_zero.1 hm with h | h
    · have hy : yA = yB := sub_eq_zero.1 h
      subst hy
      exact hd (sub_self _)
    · have hy : yA = W.toAffine.negY xA yB := by
        rw [WeierstrassCurve.Affine.negY]
        linear_combination h + xA * h1 + h3
      exact hs (WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hy)
  · have hx' : xA - xB ≠ 0 := sub_ne_zero.2 hx
    rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.add_of_X_ne hx,
      WeierstrassCurve.Affine.Point.add_of_X_ne hx]
    simp only [px, py, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope_of_X_ne hx,
      WeierstrassCurve.Affine.negY, h1, h2, h3]
    field_simp
    ring

variable {C : Type} [NormedField C] [IsUltrametricDist C]

/- English proof (translation)
Take `⟨-, -, -, h4, h6⟩` from `hW`. Establish `hc` using `chord_identity W h1 h2 h3 A B hA hB hs hd`. Generalize the expression as in `A - B = D at hc hd hdx ⊢`. Break down `D with _ | ⟨xd, yd, hdn⟩` into its components or cases. Conclude with `absurd rfl hd`.

Establish `hX : 1 < ‖xd‖` using `hdx`. Establish `hX0 : 0 < ‖xd‖` using `by linarith`. Establish `hXne : ‖xd‖ ≠ 0` using `hX0.ne'`. Establish `hc' : (px W A - px W B) ^ 2 * (px W (A + B) - xd) = -4 * py W A * py W B` using `hc`. Establish `eqd` using `(WeierstrassCurve.Affine.equation_iff _ _).1 hdn.1`.

Establish `e : yd ^ 2 = xd ^ 3 + (W.a₄ * xd + W.a₆)`. Take the linear combination `eqd - xd * yd * h1 - yd * h3 + xd ^ 2 * h2`. Establish `hr : ‖W.a₄ * xd + W.a₆‖ ≤ ‖xd‖`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_of_le_one_left (norm_nonneg _) h4`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX2 : 1 < ‖xd‖ ^ 2` using `by nlinarith`. Establish `hX3 : ‖xd‖ < ‖xd‖ ^ 3`. Establish `hm` using `mul_lt_mul_of_pos_left hX2 hX0`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hne2 : ‖xd ^ 3‖ ≠ ‖W.a₄ * xd + W.a₆‖`. Rewrite using `[norm_pow]`. Conclude with `ne_of_gt (lt_of_le_of_lt hr hX3)`. Establish `hY : ‖yd‖ ^ 2 = ‖xd‖ ^ 3`.

Rewrite using `[← norm_pow, e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne2, norm_pow, max_eq_left (by linarith)]`. Establish `hYpos : 0 < ‖yd‖`. Assume the negation of the conclusion as `hneg`. Establish `h0 : ‖yd‖ = 0` using `le_antisymm (not_lt.1 hneg) (norm_nonneg _)`. Rewrite `hY` using `[h0]`.

Use `pow_pos hX0 3` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hne1 : ‖px W (A + B)‖ ≠ ‖-xd‖` using `ne_of_lt (by rw [norm_neg]; linarith)`. Establish `hxs : ‖px W (A + B) - xd‖ = ‖xd‖`. Rewrite using `[sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne1, norm_neg, max_eq_right (by linarith)]`.

Establish `h2n : ‖(2 : C)‖ ≤ 1`. Establish `h` using `IsUltrametricDist.norm_add_le_max (1 : C) 1`. Rewrite `h` using `[one_add_one_eq_two, norm_one, max_self]`. Conclude with `h`. Establish `h4n : ‖(4 : C)‖ ≤ 1`.

Establish `h` using `IsUltrametricDist.norm_add_le_max (2 : C) 2`. Rewrite `h` using `[show (2 : C) + 2 = 4 by norm_num]`. Conclude with `h.trans (max_le h2n h2n)`. Establish `hn` using `congrArg norm hc'`. Rewrite `hn` using `[norm_mul, norm_pow, hxs, norm_mul, norm_mul, norm_neg]`.

Establish `ha0` using `norm_nonneg (py W A)`. Establish `hb0` using `norm_nonneg (py W B)`. Establish `h40` using `norm_nonneg (4 : C)`. Establish `hab : ‖(4 : C)‖ * ‖py W A‖ ≤ 1` using `by nlinarith`. Establish `habc : ‖(4 : C)‖ * ‖py W A‖ * ‖py W B‖ ≤ 1` using `by nlinarith [mul_nonneg h40 ha0]`.

Establish `hbound : ‖px W A - px W B‖ ^ 2 * ‖xd‖ ≤ 1` using `by rw [hn]; exact habc`. Use `show ‖px W A - px W B‖ ≤ ‖-xd / yd‖`. Rewrite using `[norm_div, norm_neg]`. Establish `hq : (‖xd‖ / ‖yd‖) ^ 2 * ‖xd‖ = 1`. Rewrite using `[div_pow, hY]`.

Use `first`. Consider the case `(field_simp; ring)`. Consider the case `field_simp`. Establish `hs0` using `norm_nonneg (px W A - px W B)`. Establish `hq0 : 0 ≤ ‖xd‖ / ‖yd‖` using `div_nonneg (norm_nonneg _) (norm_nonneg _)`.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hsq : (‖xd‖ / ‖yd‖) ^ 2 < ‖px W A - px W B‖ ^ 2`. Use polynomial arithmetic with `[mul_pos (sub_pos.2 hlt) (by linarith : 0 < ‖px W A - px W B‖ + ‖xd‖ / ‖yd‖)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_x_sub_le_of_formalGroup (W : WeierstrassCurve C) (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (h3 : W.a₃ = 0)
    (hW : IntegralModel W) (A B : W.toAffine.Point) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAy : ‖py W A‖ ≤ 1) (hBy : ‖py W B‖ ≤ 1) (hs : A + B ≠ 0) (hsx : ‖px W (A + B)‖ ≤ 1)
    (hd : A - B ≠ 0) (hdx : InFormalGroupPoints (A - B)) : ‖px W A - px W B‖ ≤ ‖uOf (A - B)‖ := by
  obtain ⟨-, -, -, h4, h6⟩ := hW
  have hc := chord_identity W h1 h2 h3 A B hA hB hs hd
  generalize A - B = D at hc hd hdx ⊢
  rcases D with _ | ⟨xd, yd, hdn⟩
  · exact absurd rfl hd
  have hX : 1 < ‖xd‖ := hdx
  have hX0 : 0 < ‖xd‖ := by linarith
  have hXne : ‖xd‖ ≠ 0 := hX0.ne'
  have hc' : (px W A - px W B) ^ 2 * (px W (A + B) - xd) = -4 * py W A * py W B := hc
  have eqd := (WeierstrassCurve.Affine.equation_iff _ _).1 hdn.1
  have e : yd ^ 2 = xd ^ 3 + (W.a₄ * xd + W.a₆) := by
    linear_combination eqd - xd * yd * h1 - yd * h3 + xd ^ 2 * h2
  have hr : ‖W.a₄ * xd + W.a₆‖ ≤ ‖xd‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) h4
    · linarith
  have hX2 : 1 < ‖xd‖ ^ 2 := by nlinarith
  have hX3 : ‖xd‖ < ‖xd‖ ^ 3 := by
    have hm := mul_lt_mul_of_pos_left hX2 hX0
    nlinarith
  have hne2 : ‖xd ^ 3‖ ≠ ‖W.a₄ * xd + W.a₆‖ := by
    rw [norm_pow]
    exact ne_of_gt (lt_of_le_of_lt hr hX3)
  have hY : ‖yd‖ ^ 2 = ‖xd‖ ^ 3 := by
    rw [← norm_pow, e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne2, norm_pow,
      max_eq_left (by linarith)]
  have hYpos : 0 < ‖yd‖ := by
    by_contra hneg
    have h0 : ‖yd‖ = 0 := le_antisymm (not_lt.1 hneg) (norm_nonneg _)
    rw [h0] at hY
    have := pow_pos hX0 3
    nlinarith
  have hne1 : ‖px W (A + B)‖ ≠ ‖-xd‖ := ne_of_lt (by rw [norm_neg]; linarith)
  have hxs : ‖px W (A + B) - xd‖ = ‖xd‖ := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne1, norm_neg,
      max_eq_right (by linarith)]
  have h2n : ‖(2 : C)‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (1 : C) 1
    rw [one_add_one_eq_two, norm_one, max_self] at h
    exact h
  have h4n : ‖(4 : C)‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (2 : C) 2
    rw [show (2 : C) + 2 = 4 by norm_num] at h
    exact h.trans (max_le h2n h2n)
  have hn := congrArg norm hc'
  rw [norm_mul, norm_pow, hxs, norm_mul, norm_mul, norm_neg] at hn
  have ha0 := norm_nonneg (py W A)
  have hb0 := norm_nonneg (py W B)
  have h40 := norm_nonneg (4 : C)
  have hab : ‖(4 : C)‖ * ‖py W A‖ ≤ 1 := by nlinarith
  have habc : ‖(4 : C)‖ * ‖py W A‖ * ‖py W B‖ ≤ 1 := by nlinarith [mul_nonneg h40 ha0]
  have hbound : ‖px W A - px W B‖ ^ 2 * ‖xd‖ ≤ 1 := by rw [hn]; exact habc
  show ‖px W A - px W B‖ ≤ ‖-xd / yd‖
  rw [norm_div, norm_neg]
  have hq : (‖xd‖ / ‖yd‖) ^ 2 * ‖xd‖ = 1 := by
    rw [div_pow, hY]
    first
      | (field_simp; ring)
      | field_simp
  have hs0 := norm_nonneg (px W A - px W B)
  have hq0 : 0 ≤ ‖xd‖ / ‖yd‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
  by_contra hlt
  push_neg at hlt
  have hsq : (‖xd‖ / ‖yd‖) ^ 2 < ‖px W A - px W B‖ ^ 2 := by
    nlinarith [mul_pos (sub_pos.2 hlt) (by linarith : 0 < ‖px W A - px W B‖ + ‖xd‖ / ‖yd‖)]
  nlinarith

end ReciprocityTheory.ChartRestriction.L1
