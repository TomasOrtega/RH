import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroup

namespace GroundTheory.Arith.Abelian

noncomputable section

section Field

variable {K : Type*} [Field K] (V : WeierstrassCurve K)

open WeierstrassCurve.Affine

/- English proof (translation)
Establish `key : (-1 / w) ^ 2 + V.a₁ * (z / w) * (-1 / w) + V.a₃ * (-1 / w) - ((z / w) ^ 3 + V.a₂ * (z / w) ^ 2 + V.a₄ * (z / w) + V.a₆) = -zwPoly V z w / w ^ 3`. Unfold `zwPoly`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[WeierstrassCurve.Affine.equation_iff]`.

Rewrite `key` using `[h, neg_zero, zero_div, sub_eq_zero]`. Conclude with `key`.
-/
theorem equation_of_zwPoly {z w : K} (h : zwPoly V z w = 0) (hw : w ≠ 0) :
    V.toAffine.Equation (z / w) (-1 / w) := by
  have key : (-1 / w) ^ 2 + V.a₁ * (z / w) * (-1 / w) + V.a₃ * (-1 / w) -
      ((z / w) ^ 3 + V.a₂ * (z / w) ^ 2 + V.a₄ * (z / w) + V.a₆) = -zwPoly V z w / w ^ 3 := by
    unfold zwPoly; field_simp; ring
  rw [WeierstrassCurve.Affine.equation_iff]
  rw [h, neg_zero, zero_div, sub_eq_zero] at key
  exact key

variable [V.IsElliptic]

open Classical in

noncomputable def zwPoint (z w : K) : V.toAffine.Point :=
  if h : zwPoly V z w = 0 ∧ w ≠ 0 then Point.mk (equation_of_zwPoly V h.1 h.2) else 0

/- English proof (translation)
Rewrite using `[zwPoint, dif_pos ⟨h, hw⟩]`.
-/
theorem zwPoint_of {z w : K} (h : zwPoly V z w = 0) (hw : w ≠ 0) :
    zwPoint V z w = Point.mk (equation_of_zwPoly V h hw) := by
  rw [zwPoint, dif_pos ⟨h, hw⟩]

/- English proof (translation)
Substitute `hl₁ hl₂` using the available equality. Use `set B := secantB V l with hB`. Use `set A := secantA V l n with hA`. Use `set Cc := V.a₁ * n + 2 * V.a₃ * l * n + V.a₄ * n ^ 2 + 3 * V.a₆ * l * n ^ 2 - l with hCc`. Use `set D := V.a₃ * n ^ 2 + V.a₆ * n ^ 3 - n with hD`.

Establish `hf : ∀ t, zwPoly V t (l * t + n) = B * t ^ 3 + A * t ^ 2 + Cc * t + D`. Introduce `t`. Simplify using `only [zwPoly, hB, hA, hCc, hD, secantB, secantA]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : A + B * (z₁ + z₂ + z₃) = 0`.

Rewrite using `[hz₃]`. Take the linear combination `(-A) * hb`. Use `set α := Cc - B * (z₁ * z₂ + z₁ * z₃ + z₂ * z₃) with hα`. Use `set β := D + B * z₁ * z₂ * z₃ with hβ`. Establish `hg : ∀ t, zwPoly V t (l * t + n) = B * (t - z₁) * (t - z₂) * (t - z₃) + α * t + β`.

Introduce `t`. Rewrite using `[hf]`. Take the linear combination `t ^ 2 * hs`. Establish `hz : z₁ ≠ z₂`. Introduce and unpack `rfl`.

Conclude with `hx rfl`. Establish `e₁ : α * z₁ + β = 0`. Use `hg z₁` as an intermediate fact. Rewrite `this` using `[h₁]`. Take the linear combination `-this`.

Establish `e₂ : α * z₂ + β = 0`. Use `hg z₂` as an intermediate fact. Rewrite `this` using `[h₂]`. Take the linear combination `-this`. Establish `hα0 : α = 0`.

Establish `: α * (z₁ - z₂) = 0` using `by linear_combination e₁ - e₂`. Conclude with `(mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hz)`. Establish `hβ0 : β = 0` using `by rw [hα0, zero_mul, zero_add] at e₁; exact e₁`. Establish `hcub : ∀ t, zwPoly V t (l * t + n) = B * (t - z₁) * (t - z₂) * (t - z₃)`. Introduce `t`.

Rewrite using `[hg, hα0, hβ0]`. Expand and normalize the polynomial expressions, which then agree. Establish `h₃ : zwPoly V z₃ w₃ = 0` using `by rw [hw₃def, hcub]; ring`. Establish `hn : n ≠ 0`. Introduce `hn`.

Establish `hz₁ : z₁ ≠ 0` using `by rintro rfl; apply hw₁; rw [hn]; ring`. Establish `hz₂ : z₂ ≠ 0` using `by rintro rfl; apply hw₂; rw [hn]; ring`. Establish `hl : l ≠ 0` using `by rintro rfl; apply hw₁; rw [hn]; ring`. Apply `hx` to reduce the goal to its premises. Rewrite using `[hn, add_zero, add_zero, div_eq_div_iff (mul_ne_zero hl hz₁) (mul_ne_zero hl hz₂)]`.

Expand and normalize the polynomial expressions, which then agree. Use `set x₁ := z₁ / (l * z₁ + n) with hx₁`. Use `set x₂ := z₂ / (l * z₂ + n) with hx₂`. Use `set y₁ := -1 / (l * z₁ + n) with hy₁`. Use `set y₂ := -1 / (l * z₂ + n) with hy₂`.

Establish `E₁ : V.toAffine.Equation x₁ y₁` using `equation_of_zwPoly V h₁ hw₁`. Establish `E₂ : V.toAffine.Equation x₂ y₂` using `equation_of_zwPoly V h₂ hw₂`. Use `set ℓ := l / n with hℓ`. Use `set m := -1 / n with hm`. Establish `line₁ : y₁ = ℓ * x₁ + m`.

Simplify using `only [hy₁, hx₁, hℓ, hm]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `line₂ : y₂ = ℓ * x₂ + m`. Simplify using `only [hy₂, hx₂, hℓ, hm]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hslope : V.toAffine.slope x₁ x₂ y₁ y₂ = ℓ`. Rewrite using `[WeierstrassCurve.Affine.slope_of_X_ne hx, line₁, line₂, show ℓ * x₁ + m - (ℓ * x₂ + m) = ℓ * (x₁ - x₂) by ring, mul_div_assoc, div_self (sub_ne_zero.2 hx), mul_one]`. Establish `hpoly` using `WeierstrassCurve.Affine.addPolynomial_slope E₁ E₂ (fun h => hx h.1)`.

Rewrite `hpoly` using `[hslope, WeierstrassCurve.Affine.addPolynomial_eq]`. Use `set X' := V.toAffine.addX x₁ x₂ ℓ with hX'`. Establish `hev : ∀ x, x ^ 3 + (-ℓ ^ 2 - V.a₁ * ℓ + V.a₂) * x ^ 2 + (2 * x₁ * ℓ ^ 2 + (V.a₁ * x₁ - 2 * y₁ - V.a₃) * ℓ + (-V.a₁ * y₁ + V.a₄)) * x + (-x₁ ^ 2 * ℓ ^ 2 + (2 * x₁ * y₁ + V.a₃ * x₁) * ℓ - (y₁ ^ 2 + V.a₃ * y₁ - V.a₆)) = (x - x₁) * (x - x₂) * (x - X')`. Introduce `x`. Use `congrArg (Polynomial.eval x) hpoly` as an intermediate fact.

Simplify using `[Cubic.toPoly] at this`. Apply the tactic sequence `first | linear_combination this | linear_combination -this`. Establish `hft : ∀ t, l * t + n ≠ 0 → zwPoly V t (l * t + n) = (t - x₁ * (l * t + n)) * (t - x₂ * (l * t + n)) * (t - X' * (l * t + n))`. Introduce `t hs`. Generalize the expression as in `hsd : l * t + n = s at hs ⊢`.

Establish `h0` using `hev (t / s)`. Establish `key : zwPoly V t s = s ^ 3 * ((t / s) ^ 3 + (-ℓ ^ 2 - V.a₁ * ℓ + V.a₂) * (t / s) ^ 2 + (2 * x₁ * ℓ ^ 2 + (V.a₁ * x₁ - 2 * y₁ - V.a₃) * ℓ + (-V.a₁ * y₁ + V.a₄)) * (t / s) + (-x₁ ^ 2 * ℓ ^ 2 + (2 * x₁ * y₁ + V.a₃ * x₁) * ℓ - (y₁ ^ 2 + V.a₃ * y₁ - V.a₆)))`. Rewrite using `[line₁]`. Simplify using `only [zwPoly, hℓ, hm]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[← hsd]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, h0]`. Clear the denominators using the available nonvanishing facts. Establish `fac₁ : ∀ t, t - x₁ * (l * t + n) = n / (l * z₁ + n) * (t - z₁)`.

Introduce `t`. Establish `hx1 : x₁ * (l * z₁ + n) = z₁` using `div_mul_cancel₀ _ hw₁`. Establish `hd : n / (l * z₁ + n) * (l * z₁ + n) = n` using `div_mul_cancel₀ _ hw₁`. Apply `mul_right_cancel₀ hw₁` to reduce the goal to its premises. Take the linear combination `(-(l * t + n)) * hx1 + (-(t - z₁)) * hd`.

Establish `fac₂ : ∀ t, t - x₂ * (l * t + n) = n / (l * z₂ + n) * (t - z₂)`. Introduce `t`. Establish `hx2 : x₂ * (l * z₂ + n) = z₂` using `div_mul_cancel₀ _ hw₂`. Establish `hd : n / (l * z₂ + n) * (l * z₂ + n) = n` using `div_mul_cancel₀ _ hw₂`. Apply `mul_right_cancel₀ hw₂` to reduce the goal to its premises.

Take the linear combination `(-(l * t + n)) * hx2 + (-(t - z₂)) * hd`. Use `set c := n / (l * z₁ + n) * (n / (l * z₂ + n)) with hc`. Establish `hc0 : c ≠ 0` using `mul_ne_zero (div_ne_zero hn hw₁) (div_ne_zero hn hw₂)`. Establish `key : ∀ t, t ≠ z₁ → t ≠ z₂ → l * t + n ≠ 0 → B * (t - z₃) = c * (t - X' * (l * t + n))`. Introduce `t ht₁ ht₂ hs`.

Establish `e` using `(hcub t).symm.trans (hft t hs)`. Rewrite `e` using `[fac₁, fac₂]`. Establish `: (t - z₁) * (t - z₂) * (B * (t - z₃) - c * (t - X' * (l * t + n))) = 0`. Simplify using `only [hc]`. Take the linear combination `e`.

Break down `mul_eq_zero.1 this with h | h` into its components or cases. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h) ht₁`. Conclude with `absurd (sub_eq_zero.1 h) ht₂`. Conclude with `sub_eq_zero.1 h`.

Establish `good : ∀ t, t ≠ -n / l → l * t + n ≠ 0`. Introduce `t ht h`. Distinguish the cases in `hl : l = 0`. Rewrite `h` using `[hl, zero_mul, zero_add]`. Conclude with `hn h`.

Apply `ht` to reduce the goal to its premises. Clear the denominators using the available nonvanishing facts. Take the linear combination `h`. Take `⟨ta, hta⟩` from `Infinite.exists_notMem_finset ({z₁, z₂, -n / l} : Finset K)`. Take `⟨tb, htb⟩` from `Infinite.exists_notMem_finset ({z₁, z₂, -n / l, ta} : Finset K)`.

Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or] at hta htb`. Establish `ka` using `key ta hta.1 hta.2.1 (good ta hta.2.2)`. Establish `kb` using `key tb htb.1 htb.2.1 (good tb htb.2.2.1)`. Establish `hB' : B = c * (1 - X' * l)`. Establish `: (ta - tb) * (B - c * (1 - X' * l)) = 0` using `by linear_combination ka - kb`.

Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm htb.2.2.2)))`. Establish `hz₃c : c * ((1 - X' * l) * z₃ - X' * n) = 0` using `by linear_combination -ka + (ta - z₃) * hB'`. Establish `hz₃X : z₃ = X' * w₃`. Use `(mul_eq_zero.1 hz₃c).resolve_left hc0` as an intermediate fact. Rewrite using `[hw₃def]`.

Take the linear combination `this`. Establish `hw₃ : w₃ ≠ 0`. Introduce `h0`. Establish `hz0 : z₃ = 0` using `by rw [hz₃X, h0, mul_zero]`. Apply `hn` to reduce the goal to its premises.

Establish `: w₃ = n` using `by rw [hw₃def, hz0]; ring`. Rewrite using `[← this, h0]`. Use `⟨h₃, hw₃, ?_⟩` and prove the remaining obligations. Establish `E₃ : V.toAffine.Equation (z₃ / w₃) (-1 / w₃)` using `equation_of_zwPoly V h₃ hw₃`. Establish `P₁ : zwPoint V z₁ (l * z₁ + n) = Point.mk E₁` using `zwPoint_of V h₁ hw₁`.

Establish `P₂ : zwPoint V z₂ (l * z₂ + n) = Point.mk E₂` using `zwPoint_of V h₂ hw₂`. Establish `P₃ : zwPoint V z₃ w₃ = Point.mk E₃` using `zwPoint_of V h₃ hw₃`. Rewrite using `[P₁, P₂, P₃]`. Simplify using `only [WeierstrassCurve.Affine.Point.mk]`. Rewrite using `[WeierstrassCurve.Affine.Point.add_of_X_ne' hx]`.

Use `congr 1`. Rewrite using `[WeierstrassCurve.Affine.Point.some.injEq, hslope]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_div_iff hw₃]`. Conclude with `hz₃X.symm`.

Simplify using `only [WeierstrassCurve.Affine.negAddY]`. Rewrite using `[← hX', line₁, eq_div_iff hw₃]`. Establish `: (ℓ * (X' - x₁) + (ℓ * x₁ + m)) * w₃ = ℓ * (X' * w₃) + m * w₃` using `by ring`. Rewrite using `[this, ← hz₃X]`. Establish `hw₃'` using `hw₃`.

Rewrite `hw₃'`, the goal using `[hw₃def]`. Simplify using `only [hℓ, hm]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem secant_spec [DecidableEq K] [Infinite K] {z₁ w₁ z₂ w₂ l n b z₃ w₃ : K}
    (h₁ : zwPoly V z₁ w₁ = 0) (h₂ : zwPoly V z₂ w₂ = 0) (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0)
    (hl₁ : w₁ = l * z₁ + n) (hl₂ : w₂ = l * z₂ + n) (hb : secantB V l * b = 1)
    (hx : z₁ / w₁ ≠ z₂ / w₂) (hz₃ : z₃ = -z₁ - z₂ - secantA V l n * b)
    (hw₃def : w₃ = l * z₃ + n) :
    zwPoly V z₃ w₃ = 0 ∧ w₃ ≠ 0 ∧
      zwPoint V z₁ w₁ + zwPoint V z₂ w₂ = -zwPoint V z₃ w₃ := by
  subst hl₁ hl₂

  set B := secantB V l with hB
  set A := secantA V l n with hA
  set Cc := V.a₁ * n + 2 * V.a₃ * l * n + V.a₄ * n ^ 2 + 3 * V.a₆ * l * n ^ 2 - l with hCc
  set D := V.a₃ * n ^ 2 + V.a₆ * n ^ 3 - n with hD
  have hf : ∀ t, zwPoly V t (l * t + n) = B * t ^ 3 + A * t ^ 2 + Cc * t + D := by
    intro t; simp only [zwPoly, hB, hA, hCc, hD, secantB, secantA]; ring
  have hs : A + B * (z₁ + z₂ + z₃) = 0 := by
    rw [hz₃]; linear_combination (-A) * hb
  set α := Cc - B * (z₁ * z₂ + z₁ * z₃ + z₂ * z₃) with hα
  set β := D + B * z₁ * z₂ * z₃ with hβ
  have hg : ∀ t, zwPoly V t (l * t + n) = B * (t - z₁) * (t - z₂) * (t - z₃) + α * t + β := by
    intro t; rw [hf]; linear_combination t ^ 2 * hs
  have hz : z₁ ≠ z₂ := by
    rintro rfl; exact hx rfl
  have e₁ : α * z₁ + β = 0 := by
    have := hg z₁; rw [h₁] at this; linear_combination -this
  have e₂ : α * z₂ + β = 0 := by
    have := hg z₂; rw [h₂] at this; linear_combination -this
  have hα0 : α = 0 := by
    have : α * (z₁ - z₂) = 0 := by linear_combination e₁ - e₂
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hz)
  have hβ0 : β = 0 := by rw [hα0, zero_mul, zero_add] at e₁; exact e₁
  have hcub : ∀ t, zwPoly V t (l * t + n) = B * (t - z₁) * (t - z₂) * (t - z₃) := by
    intro t; rw [hg, hα0, hβ0]; ring
  have h₃ : zwPoly V z₃ w₃ = 0 := by rw [hw₃def, hcub]; ring

  have hn : n ≠ 0 := by
    intro hn
    have hz₁ : z₁ ≠ 0 := by rintro rfl; apply hw₁; rw [hn]; ring
    have hz₂ : z₂ ≠ 0 := by rintro rfl; apply hw₂; rw [hn]; ring
    have hl : l ≠ 0 := by rintro rfl; apply hw₁; rw [hn]; ring
    apply hx; rw [hn, add_zero, add_zero, div_eq_div_iff (mul_ne_zero hl hz₁)
      (mul_ne_zero hl hz₂)]; ring

  set x₁ := z₁ / (l * z₁ + n) with hx₁
  set x₂ := z₂ / (l * z₂ + n) with hx₂
  set y₁ := -1 / (l * z₁ + n) with hy₁
  set y₂ := -1 / (l * z₂ + n) with hy₂
  have E₁ : V.toAffine.Equation x₁ y₁ := equation_of_zwPoly V h₁ hw₁
  have E₂ : V.toAffine.Equation x₂ y₂ := equation_of_zwPoly V h₂ hw₂
  set ℓ := l / n with hℓ
  set m := -1 / n with hm
  have line₁ : y₁ = ℓ * x₁ + m := by
    simp only [hy₁, hx₁, hℓ, hm]; field_simp; ring
  have line₂ : y₂ = ℓ * x₂ + m := by
    simp only [hy₂, hx₂, hℓ, hm]; field_simp; ring
  have hslope : V.toAffine.slope x₁ x₂ y₁ y₂ = ℓ := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx, line₁, line₂,
      show ℓ * x₁ + m - (ℓ * x₂ + m) = ℓ * (x₁ - x₂) by ring, mul_div_assoc,
      div_self (sub_ne_zero.2 hx), mul_one]
  have hpoly := WeierstrassCurve.Affine.addPolynomial_slope E₁ E₂ (fun h => hx h.1)
  rw [hslope, WeierstrassCurve.Affine.addPolynomial_eq] at hpoly
  set X' := V.toAffine.addX x₁ x₂ ℓ with hX'
  have hev : ∀ x, x ^ 3 + (-ℓ ^ 2 - V.a₁ * ℓ + V.a₂) * x ^ 2 +
      (2 * x₁ * ℓ ^ 2 + (V.a₁ * x₁ - 2 * y₁ - V.a₃) * ℓ + (-V.a₁ * y₁ + V.a₄)) * x +
      (-x₁ ^ 2 * ℓ ^ 2 + (2 * x₁ * y₁ + V.a₃ * x₁) * ℓ - (y₁ ^ 2 + V.a₃ * y₁ - V.a₆)) =
      (x - x₁) * (x - x₂) * (x - X') := by
    intro x
    have := congrArg (Polynomial.eval x) hpoly
    simp [Cubic.toPoly] at this
    first | linear_combination this | linear_combination -this
  have hft : ∀ t, l * t + n ≠ 0 → zwPoly V t (l * t + n) =
      (t - x₁ * (l * t + n)) * (t - x₂ * (l * t + n)) * (t - X' * (l * t + n)) := by
    intro t hs
    generalize hsd : l * t + n = s at hs ⊢
    have h0 := hev (t / s)
    have key : zwPoly V t s = s ^ 3 * ((t / s) ^ 3 +
        (-ℓ ^ 2 - V.a₁ * ℓ + V.a₂) * (t / s) ^ 2 +
        (2 * x₁ * ℓ ^ 2 + (V.a₁ * x₁ - 2 * y₁ - V.a₃) * ℓ + (-V.a₁ * y₁ + V.a₄)) * (t / s) +
        (-x₁ ^ 2 * ℓ ^ 2 + (2 * x₁ * y₁ + V.a₃ * x₁) * ℓ - (y₁ ^ 2 + V.a₃ * y₁ - V.a₆))) := by
      rw [line₁]; simp only [zwPoly, hℓ, hm]; field_simp; rw [← hsd]; ring
    rw [key, h0]; field_simp
  have fac₁ : ∀ t, t - x₁ * (l * t + n) = n / (l * z₁ + n) * (t - z₁) := by
    intro t
    have hx1 : x₁ * (l * z₁ + n) = z₁ := div_mul_cancel₀ _ hw₁
    have hd : n / (l * z₁ + n) * (l * z₁ + n) = n := div_mul_cancel₀ _ hw₁
    apply mul_right_cancel₀ hw₁
    linear_combination (-(l * t + n)) * hx1 + (-(t - z₁)) * hd
  have fac₂ : ∀ t, t - x₂ * (l * t + n) = n / (l * z₂ + n) * (t - z₂) := by
    intro t
    have hx2 : x₂ * (l * z₂ + n) = z₂ := div_mul_cancel₀ _ hw₂
    have hd : n / (l * z₂ + n) * (l * z₂ + n) = n := div_mul_cancel₀ _ hw₂
    apply mul_right_cancel₀ hw₂
    linear_combination (-(l * t + n)) * hx2 + (-(t - z₂)) * hd
  set c := n / (l * z₁ + n) * (n / (l * z₂ + n)) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (div_ne_zero hn hw₁) (div_ne_zero hn hw₂)
  have key : ∀ t, t ≠ z₁ → t ≠ z₂ → l * t + n ≠ 0 → B * (t - z₃) = c * (t - X' * (l * t + n)) := by
    intro t ht₁ ht₂ hs
    have e := (hcub t).symm.trans (hft t hs)
    rw [fac₁, fac₂] at e
    have : (t - z₁) * (t - z₂) * (B * (t - z₃) - c * (t - X' * (l * t + n))) = 0 := by
      simp only [hc]; linear_combination e
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd (sub_eq_zero.1 h) ht₁
      · exact absurd (sub_eq_zero.1 h) ht₂
    · exact sub_eq_zero.1 h
  have good : ∀ t, t ≠ -n / l → l * t + n ≠ 0 := by
    intro t ht h
    by_cases hl : l = 0
    · rw [hl, zero_mul, zero_add] at h; exact hn h
    · apply ht; field_simp; linear_combination h
  obtain ⟨ta, hta⟩ := Infinite.exists_notMem_finset ({z₁, z₂, -n / l} : Finset K)
  obtain ⟨tb, htb⟩ := Infinite.exists_notMem_finset ({z₁, z₂, -n / l, ta} : Finset K)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hta htb
  have ka := key ta hta.1 hta.2.1 (good ta hta.2.2)
  have kb := key tb htb.1 htb.2.1 (good tb htb.2.2.1)
  have hB' : B = c * (1 - X' * l) := by
    have : (ta - tb) * (B - c * (1 - X' * l)) = 0 := by linear_combination ka - kb
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm htb.2.2.2)))
  have hz₃c : c * ((1 - X' * l) * z₃ - X' * n) = 0 := by linear_combination -ka + (ta - z₃) * hB'
  have hz₃X : z₃ = X' * w₃ := by
    have := (mul_eq_zero.1 hz₃c).resolve_left hc0
    rw [hw₃def]; linear_combination this
  have hw₃ : w₃ ≠ 0 := by
    intro h0
    have hz0 : z₃ = 0 := by rw [hz₃X, h0, mul_zero]
    apply hn
    have : w₃ = n := by rw [hw₃def, hz0]; ring
    rw [← this, h0]
  refine ⟨h₃, hw₃, ?_⟩
  have E₃ : V.toAffine.Equation (z₃ / w₃) (-1 / w₃) := equation_of_zwPoly V h₃ hw₃
  have P₁ : zwPoint V z₁ (l * z₁ + n) = Point.mk E₁ := zwPoint_of V h₁ hw₁
  have P₂ : zwPoint V z₂ (l * z₂ + n) = Point.mk E₂ := zwPoint_of V h₂ hw₂
  have P₃ : zwPoint V z₃ w₃ = Point.mk E₃ := zwPoint_of V h₃ hw₃
  rw [P₁, P₂, P₃]
  simp only [WeierstrassCurve.Affine.Point.mk]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne' hx]
  congr 1
  rw [WeierstrassCurve.Affine.Point.some.injEq, hslope]
  refine ⟨?_, ?_⟩
  · rw [eq_div_iff hw₃]; exact hz₃X.symm
  · simp only [WeierstrassCurve.Affine.negAddY]
    rw [← hX', line₁, eq_div_iff hw₃]
    have : (ℓ * (X' - x₁) + (ℓ * x₁ + m)) * w₃ = ℓ * (X' * w₃) + m * w₃ := by ring
    rw [this, ← hz₃X]
    have hw₃' := hw₃
    rw [hw₃def] at hw₃' ⊢
    simp only [hℓ, hm]
    field_simp
    ring

omit [V.IsElliptic] in
/- English proof (translation)
Establish `hc : 1 - V.a₁ * z - V.a₃ * w ≠ 0` using `left_ne_zero_of_mul_eq_one he`. Establish `he' : e = (1 - V.a₁ * z - V.a₃ * w)⁻¹` using `eq_inv_of_mul_eq_one_right he`. Substitute `he'` using the available equality. Unfold `zwPoly`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem zwPoly_neg {z w e : K} (he : (1 - V.a₁ * z - V.a₃ * w) * e = 1) :
    zwPoly V (-z * e) (-w * e) = -e ^ 3 * zwPoly V z w := by
  have hc : 1 - V.a₁ * z - V.a₃ * w ≠ 0 := left_ne_zero_of_mul_eq_one he
  have he' : e = (1 - V.a₁ * z - V.a₃ * w)⁻¹ := eq_inv_of_mul_eq_one_right he
  subst he'
  unfold zwPoly
  field_simp
  ring

/- English proof (translation)
Establish `he0 : e ≠ 0` using `right_ne_zero_of_mul_eq_one he`. Establish `h' : zwPoly V (-z * e) (-w * e) = 0` using `by rw [zwPoly_neg V he, h, mul_zero]`. Establish `hw' : -w * e ≠ 0` using `mul_ne_zero (neg_ne_zero.2 hw) he0`. Use `⟨h', hw', ?_⟩` and prove the remaining obligations. Rewrite using `[zwPoint_of V h hw, zwPoint_of V h' hw']`.

Simplify using `only [WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.neg_some]`. Rewrite using `[WeierstrassCurve.Affine.Point.some.injEq]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Rewrite using `[WeierstrassCurve.Affine.negY]`.

Establish `hc : 1 - V.a₁ * z - V.a₃ * w ≠ 0` using `left_ne_zero_of_mul_eq_one he`. Establish `he' : e = (1 - V.a₁ * z - V.a₃ * w)⁻¹` using `eq_inv_of_mul_eq_one_right he`. Substitute `he'` using the available equality. Clear the denominators using the available nonvanishing facts.
-/
theorem neg_zwPoint {z w e : K} (h : zwPoly V z w = 0) (hw : w ≠ 0)
    (he : (1 - V.a₁ * z - V.a₃ * w) * e = 1) :
    zwPoly V (-z * e) (-w * e) = 0 ∧ -w * e ≠ 0 ∧
      -zwPoint V z w = zwPoint V (-z * e) (-w * e) := by
  have he0 : e ≠ 0 := right_ne_zero_of_mul_eq_one he
  have h' : zwPoly V (-z * e) (-w * e) = 0 := by rw [zwPoly_neg V he, h, mul_zero]
  have hw' : -w * e ≠ 0 := mul_ne_zero (neg_ne_zero.2 hw) he0
  refine ⟨h', hw', ?_⟩
  rw [zwPoint_of V h hw, zwPoint_of V h' hw']
  simp only [WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.neg_some]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  refine ⟨?_, ?_⟩
  · field_simp
  · rw [WeierstrassCurve.Affine.negY]
    have hc : 1 - V.a₁ * z - V.a₃ * w ≠ 0 := left_ne_zero_of_mul_eq_one he
    have he' : e = (1 - V.a₁ * z - V.a₃ * w)⁻¹ := eq_inv_of_mul_eq_one_right he
    subst he'
    field_simp

end Field

section Points

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R) (τ : Type*)

/- English proof (translation)
The claim follows from `NoZeroDivisors.to_isDomain _`.
-/
theorem isDomain_mvPowerSeries : IsDomain (MvPowerSeries τ R) := NoZeroDivisors.to_isDomain _

attribute [local instance] isDomain_mvPowerSeries

/- English proof (translation)
Set `i : τ` to `Classical.arbitrary τ`. Use `Infinite.of_injective (fun n : ℕ => (MvPowerSeries.X i : MvPowerSeries τ R) ^ n) ?_` and prove the remaining obligations. Introduce `m n h`. Use `congrArg (MvPowerSeries.coeff (Finsupp.single i m)) h` as an intermediate fact. Simplify using `only [MvPowerSeries.coeff_X_pow] at this`.

Assume the negation of the conclusion as `hmn`. Rewrite `this` using `[if_neg (fun h' => hmn (Finsupp.single_injective i h'))]`. Conclude with `one_ne_zero this`.
-/
theorem infinite_mvPowerSeries [Nonempty τ] : Infinite (MvPowerSeries τ R) := by
  classical
  let i : τ := Classical.arbitrary τ
  refine Infinite.of_injective (fun n : ℕ => (MvPowerSeries.X i : MvPowerSeries τ R) ^ n) ?_
  intro m n h
  have := congrArg (MvPowerSeries.coeff (Finsupp.single i m)) h
  simp only [MvPowerSeries.coeff_X_pow] at this
  by_contra hmn
  rw [if_neg (fun h' => hmn (Finsupp.single_injective i h'))] at this
  exact one_ne_zero this

noncomputable def toFrac : R →+* FractionRing (MvPowerSeries τ R) :=
  (algebraMap (MvPowerSeries τ R) (FractionRing (MvPowerSeries τ R))).comp MvPowerSeries.C

omit [IsDomain R] in
/- English proof (translation)
The claim follows from `(IsFractionRing.injective (MvPowerSeries τ R) _).comp MvPowerSeries.C_injective`.
-/
theorem toFrac_injective : Function.Injective (toFrac (R := R) τ) :=
  (IsFractionRing.injective (MvPowerSeries τ R) _).comp MvPowerSeries.C_injective

noncomputable abbrev curveFrac : WeierstrassCurve (FractionRing (MvPowerSeries τ R)) :=
  W.map (toFrac τ)

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [curveFrac, WeierstrassCurve.map_Δ] exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (toFrac_injective τ)).2 hΔ)⟩`.
-/
theorem isElliptic_curveFrac (hΔ : W.Δ ≠ 0) : (curveFrac W τ).IsElliptic :=
  ⟨by rw [curveFrac, WeierstrassCurve.map_Δ]
      exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (toFrac_injective τ)).2 hΔ)⟩

variable [Fact (W.Δ ≠ 0)]

instance : (curveFrac W τ).IsElliptic := isElliptic_curveFrac W τ Fact.out

noncomputable def pointOf (u : MvPowerSeries τ R) : (curveFrac W τ).toAffine.Point :=
  zwPoint (curveFrac W τ) (algebraMap _ (FractionRing (MvPowerSeries τ R)) u)
    (algebraMap _ (FractionRing (MvPowerSeries τ R)) (wAt W u))

omit [IsDomain R] [Fact (W.Δ ≠ 0)] in
/- English proof (translation)
Rewrite using `[WeierstrassCurve.map_map]`. Both sides reduce to the same expression.
-/
theorem map_C_map_algebraMap :
    (W.map (MvPowerSeries.C (σ := τ))).map
      (algebraMap (MvPowerSeries τ R) (FractionRing (MvPowerSeries τ R))) = curveFrac W τ := by
  rw [WeierstrassCurve.map_map]; rfl

omit [IsDomain R] [Fact (W.Δ ≠ 0)] in
/- English proof (translation)
Use `congrArg (algebraMap (MvPowerSeries τ R) (FractionRing (MvPowerSeries τ R))) (zwPoly_wAt W hu)` as an intermediate fact. Rewrite `this` using `[map_zwPoly, map_zero, map_C_map_algebraMap]`. Then use the resulting hypothesis.
-/
theorem zwPoly_curveFrac {u : MvPowerSeries τ R} (hu : MvPowerSeries.constantCoeff u = 0) :
    zwPoly (curveFrac W τ) (algebraMap _ (FractionRing (MvPowerSeries τ R)) u)
      (algebraMap _ (FractionRing (MvPowerSeries τ R)) (wAt W u)) = 0 := by
  have := congrArg (algebraMap (MvPowerSeries τ R) (FractionRing (MvPowerSeries τ R)))
    (zwPoly_wAt W hu)
  rwa [map_zwPoly, map_zero, map_C_map_algebraMap] at this

/- English proof (translation)
Use `set ι := algebraMap (MvPowerSeries τ R) (FractionRing (MvPowerSeries τ R))`. Establish `hι : Function.Injective ι` using `IsFractionRing.injective _ _`. Establish `hw : ι (wAt W u) ≠ 0` using `(map_ne_zero_iff ι hι).2 (wAt_ne_zero W hu h0)`. Establish `hw' : ι (wAt W u') ≠ 0` using `(map_ne_zero_iff ι hι).2 (wAt_ne_zero W hu' h0')`. Rewrite `h` using `[pointOf, pointOf, zwPoint_of _ (zwPoly_curveFrac W τ hu) hw, zwPoint_of _ (zwPoly_curveFrac W τ hu') hw']`.

Simplify using `only [WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.some.injEq] at h`. Take `⟨h1, h2⟩` from `h`. Establish `e : wAt W u = wAt W u'`. Use `congrArg (fun t => -t⁻¹) h2` as an intermediate fact. Simplify `this` using `[div_eq_mul_inv]`.

Rewrite `h1` using `[e, div_left_inj' hw']`. Conclude with `hι h1`.
-/
theorem pointOf_injective {u u' : MvPowerSeries τ R} (hu : MvPowerSeries.constantCoeff u = 0)
    (hu' : MvPowerSeries.constantCoeff u' = 0) (h0 : u ≠ 0) (h0' : u' ≠ 0)
    (h : pointOf W τ u = pointOf W τ u') : u = u' := by
  set ι := algebraMap (MvPowerSeries τ R) (FractionRing (MvPowerSeries τ R))
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  have hw : ι (wAt W u) ≠ 0 := (map_ne_zero_iff ι hι).2 (wAt_ne_zero W hu h0)
  have hw' : ι (wAt W u') ≠ 0 := (map_ne_zero_iff ι hι).2 (wAt_ne_zero W hu' h0')
  rw [pointOf, pointOf, zwPoint_of _ (zwPoly_curveFrac W τ hu) hw,
    zwPoint_of _ (zwPoly_curveFrac W τ hu') hw'] at h
  simp only [WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.some.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e : wAt W u = wAt W u' := by
    have := congrArg (fun t => -t⁻¹) h2
    simpa [div_eq_mul_inv] using this
  rw [e, div_left_inj' hw'] at h1
  exact hι h1

open Classical in

/- English proof (translation)
Establish `: Infinite (MvPowerSeries τ R)` using `infinite_mvPowerSeries τ`. Establish `: Infinite (FractionRing (MvPowerSeries τ R))` using `Infinite.of_injective _ (IsFractionRing.injective (MvPowerSeries τ R) _)`. Use `set ι := algebraMap (MvPowerSeries τ R) (FractionRing (MvPowerSeries τ R)) with hιdef`. Establish `hι : Function.Injective ι` using `IsFractionRing.injective _ _`. Establish `hab` using `GroundTheory.LocalField.FormalGroup.hasSubst_pair h₁ h₂`.

Use `set ψ := MvPowerSeries.substAlgHom (R := R) hab with hψdef`. Establish `hψ : ∀ f, MvPowerSeries.subst ![u₁, u₂] f = ψ f` using `fun f => by`. Rewrite using `[hψdef, MvPowerSeries.coe_substAlgHom]`. Establish `ψX0 : ψ (MvPowerSeries.X 0) = u₁` using `by rw [← hψ, MvPowerSeries.subst_X hab]; rfl`. Establish `ψX1 : ψ (MvPowerSeries.X 1) = u₂` using `by rw [← hψ, MvPowerSeries.subst_X hab]; rfl`.

Establish `ψC : ∀ r, ψ (MvPowerSeries.C r) = MvPowerSeries.C r` using `fun r => by`. Rewrite using `[← hψ, MvPowerSeries.subst_C]`. Establish `ψw : ∀ i, ψ (wAt W (MvPowerSeries.X i)) = wAt W (![u₁, u₂] i)` using `fun i => by`. Rewrite using `[← hψ, wAt, GroundTheory.LocalField.FormalGroup.subst_powerSeries_subst (PowerSeries.HasSubst.X i) hab, MvPowerSeries.subst_X hab, wAt]`. Establish `hc0 : ∀ f : MvPowerSeries (Fin 2) R, MvPowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff (ψ f) = 0` using `fun f hf => by`.

Rewrite using `[← hψ]`. Apply the tactic sequence `exact MvPowerSeries.constantCoeff_subst_eq_zero hab (fun i => by fin_cases i <;> simpa) hf`. Use `set l := ψ (addSlope W) with hl`. Use `set n := ψ (addIntercept W) with hn`. Use `set b := ψ (MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1) with hb`.

Use `set z₃ := ψ (thirdZ W) with hz₃`. Use `set w₃ := ψ (thirdW W) with hw₃`. Use `set e := ψ (MvPowerSeries.invOfUnit (negDen W) 1) with he`. Establish `rl₁ : wAt W u₁ = l * u₁ + n`. Use `congrArg ψ (wAt_X_zero_eq W)` as an intermediate fact.

Rewrite `this` using `[map_add, map_mul, ψw, ψX0]`. Then use the resulting hypothesis. Establish `rl₂ : wAt W u₂ = l * u₂ + n`. Use `congrArg ψ (wAt_X_one_eq W)` as an intermediate fact. Rewrite `this` using `[map_add, map_mul, ψw, ψX1]`. Then use the resulting hypothesis. Establish `rb : secantB (W.map MvPowerSeries.C) l * b = 1`.

Rewrite using `[hl, hb]`. Use `congrArg ψ (mul_invOfUnit_one (constantCoeff_secantB W))` as an intermediate fact. Simplify `this` using `only [secantB, map_add, map_mul, map_pow, map_one, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, ψC]`. Establish `rz₃ : z₃ = -u₁ - u₂ - secantA (W.map MvPowerSeries.C) l n * b`. Rewrite using `[hz₃, thirdZ, hl, hn, hb]`.

Simplify using `only [secantA, map_sub, map_neg, map_mul, map_add, map_pow, map_ofNat, ψX0, ψX1, ψC, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]`. Establish `rw₃ : w₃ = l * z₃ + n` using `by rw [hw₃, thirdW, map_add, map_mul]`. Establish `re : (1 - MvPowerSeries.C W.a₁ * z₃ - MvPowerSeries.C W.a₃ * w₃) * e = 1`. Rewrite using `[hz₃, hw₃, he]`. Use `congrArg ψ (mul_invOfUnit_one (constantCoeff_negDen W))` as an intermediate fact.

Simplify `this` using `only [negDen, map_sub, map_mul, map_one, ψC]`. Establish `rF : ψ (addSeries W) = -z₃ * e` using `by rw [addSeries, map_mul, map_neg]`. Use `set V := curveFrac W τ with hV`. Establish `hw₁ : ι (wAt W u₁) ≠ 0` using `(map_ne_zero_iff ι hι).2 (wAt_ne_zero W h₁ hu₁)`. Establish `hw₂ : ι (wAt W u₂) ≠ 0` using `(map_ne_zero_iff ι hι).2 (wAt_ne_zero W h₂ hu₂)`.

Establish `hb' : secantB V (ι l) * ι b = 1`. Use `congrArg ι rb` as an intermediate fact. Rewrite `this` using `[map_mul, map_secantB, map_one, map_C_map_algebraMap]`. Then use the resulting hypothesis. Establish `hx' : ι u₁ / ι (wAt W u₁) ≠ ι u₂ / ι (wAt W u₂)`. Rewrite using `[Ne, div_eq_div_iff hw₁ hw₂]`.

Introduce `h`. Apply `hx` to reduce the goal to its premises. Apply `hι` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul]`. Take the linear combination `h`.

Establish `hz₃' : ι z₃ = -ι u₁ - ι u₂ - secantA V (ι l) (ι n) * ι b`. Rewrite using `[rz₃, map_sub, map_sub, map_neg, map_mul, map_secantA, map_C_map_algebraMap]`. Establish `hw₃' : ι w₃ = ι l * ι z₃ + ι n` using `by rw [rw₃, map_add, map_mul]`. Take `⟨h₃, hw₃0, hsum⟩` from `secant_spec V (zwPoly_curveFrac W τ h₁) (zwPoly_curveFrac W τ h₂) hw₁ hw₂ (by rw [rl₁, map_add, map_mul]) (by rw [rl₂, map_add, map_mul]) hb' hx' hz₃' hw₃'`. Establish `he' : (1 - V.a₁ * ι z₃ - V.a₃ * ι w₃) * ι e = 1`.

Use `congrArg ι re` as an intermediate fact. Rewrite `this` using `[map_mul, map_sub, map_sub, map_mul, map_mul, map_one]`. Then use the resulting hypothesis. Take `⟨h', hw', hneg⟩` from `neg_zwPoint V h₃ hw₃0 he'`. Establish `hF : MvPowerSeries.constantCoeff (ψ (addSeries W)) = 0` using `hc0 _ (constantCoeff_addSeries W)`. Establish `hS : zwPoly (W.map MvPowerSeries.C) (ψ (addSeries W)) (-w₃ * e) = 0`.

Apply `hι` to reduce the goal to its premises. Rewrite using `[map_zwPoly, map_C_map_algebraMap, map_zero, rF, map_mul, map_mul, map_neg, map_neg]`. Conclude with `h'`. Establish `hwF : wAt W (ψ (addSeries W)) = -w₃ * e`. Use `eq_of_zwPoly_eq_zero _ (zwPoly_wAt W hF) hS ?_` and prove the remaining obligations.

Use `MvPowerSeries.isUnit_iff_constantCoeff.2 ?_` and prove the remaining obligations. Establish `hw0 : MvPowerSeries.constantCoeff w₃ = 0` using `hc0 _ (constantCoeff_thirdW W)`. Simplify using `[hF, constantCoeff_wAt W hF, hw0]`. Unfold `pointOf`. Rewrite using `[hsum, hneg, hψ, hwF, rF, map_mul, map_mul, map_neg, map_neg]`.
-/
theorem pointOf_add [Nonempty τ] {u₁ u₂ : MvPowerSeries τ R}
    (h₁ : MvPowerSeries.constantCoeff u₁ = 0) (h₂ : MvPowerSeries.constantCoeff u₂ = 0)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hx : u₁ * wAt W u₂ ≠ u₂ * wAt W u₁) :
    pointOf W τ u₁ + pointOf W τ u₂ =
      pointOf W τ (MvPowerSeries.subst ![u₁, u₂] (addSeries W)) := by
  classical
  have : Infinite (MvPowerSeries τ R) := infinite_mvPowerSeries τ
  have : Infinite (FractionRing (MvPowerSeries τ R)) :=
    Infinite.of_injective _ (IsFractionRing.injective (MvPowerSeries τ R) _)
  set ι := algebraMap (MvPowerSeries τ R) (FractionRing (MvPowerSeries τ R)) with hιdef
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  have hab := GroundTheory.LocalField.FormalGroup.hasSubst_pair h₁ h₂
  set ψ := MvPowerSeries.substAlgHom (R := R) hab with hψdef
  have hψ : ∀ f, MvPowerSeries.subst ![u₁, u₂] f = ψ f := fun f => by
    rw [hψdef, MvPowerSeries.coe_substAlgHom]
  have ψX0 : ψ (MvPowerSeries.X 0) = u₁ := by rw [← hψ, MvPowerSeries.subst_X hab]; rfl
  have ψX1 : ψ (MvPowerSeries.X 1) = u₂ := by rw [← hψ, MvPowerSeries.subst_X hab]; rfl
  have ψC : ∀ r, ψ (MvPowerSeries.C r) = MvPowerSeries.C r := fun r => by
    rw [← hψ, MvPowerSeries.subst_C]
  have ψw : ∀ i, ψ (wAt W (MvPowerSeries.X i)) = wAt W (![u₁, u₂] i) := fun i => by
    rw [← hψ, wAt, GroundTheory.LocalField.FormalGroup.subst_powerSeries_subst (PowerSeries.HasSubst.X i)
      hab, MvPowerSeries.subst_X hab, wAt]
  have hc0 : ∀ f : MvPowerSeries (Fin 2) R, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (ψ f) = 0 := fun f hf => by
    rw [← hψ]
    exact MvPowerSeries.constantCoeff_subst_eq_zero hab (fun i => by fin_cases i <;> simpa) hf

  set l := ψ (addSlope W) with hl
  set n := ψ (addIntercept W) with hn
  set b := ψ (MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1) with hb
  set z₃ := ψ (thirdZ W) with hz₃
  set w₃ := ψ (thirdW W) with hw₃
  set e := ψ (MvPowerSeries.invOfUnit (negDen W) 1) with he
  have rl₁ : wAt W u₁ = l * u₁ + n := by
    have := congrArg ψ (wAt_X_zero_eq W)
    rwa [map_add, map_mul, ψw, ψX0] at this
  have rl₂ : wAt W u₂ = l * u₂ + n := by
    have := congrArg ψ (wAt_X_one_eq W)
    rwa [map_add, map_mul, ψw, ψX1] at this
  have rb : secantB (W.map MvPowerSeries.C) l * b = 1 := by
    rw [hl, hb]
    have := congrArg ψ (mul_invOfUnit_one (constantCoeff_secantB W))
    simpa only [secantB, map_add, map_mul, map_pow, map_one, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, ψC] using this
  have rz₃ : z₃ = -u₁ - u₂ - secantA (W.map MvPowerSeries.C) l n * b := by
    rw [hz₃, thirdZ, hl, hn, hb]
    simp only [secantA, map_sub, map_neg, map_mul, map_add, map_pow, map_ofNat, ψX0, ψX1, ψC,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  have rw₃ : w₃ = l * z₃ + n := by rw [hw₃, thirdW, map_add, map_mul]
  have re : (1 - MvPowerSeries.C W.a₁ * z₃ - MvPowerSeries.C W.a₃ * w₃) * e = 1 := by
    rw [hz₃, hw₃, he]
    have := congrArg ψ (mul_invOfUnit_one (constantCoeff_negDen W))
    simpa only [negDen, map_sub, map_mul, map_one, ψC] using this
  have rF : ψ (addSeries W) = -z₃ * e := by rw [addSeries, map_mul, map_neg]

  set V := curveFrac W τ with hV
  have hw₁ : ι (wAt W u₁) ≠ 0 := (map_ne_zero_iff ι hι).2 (wAt_ne_zero W h₁ hu₁)
  have hw₂ : ι (wAt W u₂) ≠ 0 := (map_ne_zero_iff ι hι).2 (wAt_ne_zero W h₂ hu₂)
  have hb' : secantB V (ι l) * ι b = 1 := by
    have := congrArg ι rb
    rwa [map_mul, map_secantB, map_one, map_C_map_algebraMap] at this
  have hx' : ι u₁ / ι (wAt W u₁) ≠ ι u₂ / ι (wAt W u₂) := by
    rw [Ne, div_eq_div_iff hw₁ hw₂]
    intro h
    apply hx
    apply hι
    rw [map_mul, map_mul]
    linear_combination h
  have hz₃' : ι z₃ = -ι u₁ - ι u₂ - secantA V (ι l) (ι n) * ι b := by
    rw [rz₃, map_sub, map_sub, map_neg, map_mul, map_secantA, map_C_map_algebraMap]
  have hw₃' : ι w₃ = ι l * ι z₃ + ι n := by rw [rw₃, map_add, map_mul]
  obtain ⟨h₃, hw₃0, hsum⟩ := secant_spec V (zwPoly_curveFrac W τ h₁) (zwPoly_curveFrac W τ h₂)
    hw₁ hw₂ (by rw [rl₁, map_add, map_mul]) (by rw [rl₂, map_add, map_mul]) hb' hx' hz₃' hw₃'
  have he' : (1 - V.a₁ * ι z₃ - V.a₃ * ι w₃) * ι e = 1 := by
    have := congrArg ι re
    rwa [map_mul, map_sub, map_sub, map_mul, map_mul, map_one] at this
  obtain ⟨h', hw', hneg⟩ := neg_zwPoint V h₃ hw₃0 he'

  have hF : MvPowerSeries.constantCoeff (ψ (addSeries W)) = 0 := hc0 _ (constantCoeff_addSeries W)
  have hS : zwPoly (W.map MvPowerSeries.C) (ψ (addSeries W)) (-w₃ * e) = 0 := by
    apply hι
    rw [map_zwPoly, map_C_map_algebraMap, map_zero, rF, map_mul, map_mul, map_neg, map_neg]
    exact h'
  have hwF : wAt W (ψ (addSeries W)) = -w₃ * e := by
    refine eq_of_zwPoly_eq_zero _ (zwPoly_wAt W hF) hS ?_
    refine MvPowerSeries.isUnit_iff_constantCoeff.2 ?_
    have hw0 : MvPowerSeries.constantCoeff w₃ = 0 := hc0 _ (constantCoeff_thirdW W)
    simp [hF, constantCoeff_wAt W hF, hw0]
  unfold pointOf
  rw [hsum, hneg, hψ, hwF, rF, map_mul, map_mul, map_neg, map_neg]

end Points

section Lin

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {τ : Type*}

/- English proof (translation)
Rewrite using `[MvPowerSeries.coeff_X]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg, if_neg h]`.

Introduce `h'`. Conclude with `h (Finsupp.single_left_injective one_ne_zero h')`.
-/
theorem coeff_single_X [DecidableEq τ] (i j : τ) :
    MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.X j : MvPowerSeries τ R) =
      if i = j then 1 else 0 := by
  rw [MvPowerSeries.coeff_X]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg, if_neg h]
    intro h'
    exact h (Finsupp.single_left_injective one_ne_zero h')

/- English proof (translation)
Simplify using `using two_le_order_addSeries_sub W`.
-/
theorem two_le_order_addSeries_sub' : (2 : ℕ∞) ≤ MvPowerSeries.order (addSeries W -
    (MvPowerSeries.C 1 * MvPowerSeries.X 0 + MvPowerSeries.C 1 * MvPowerSeries.X 1)) := by
  simpa using two_le_order_addSeries_sub W

/- English proof (translation)
Rewrite using `[coeff_single_subst_pair (two_le_order_addSeries_sub' W) h₁ h₂, one_mul, one_mul]`.
-/
theorem coeff_single_subst_addSeries [DecidableEq τ] {u₁ u₂ : MvPowerSeries τ R}
    (h₁ : MvPowerSeries.constantCoeff u₁ = 0) (h₂ : MvPowerSeries.constantCoeff u₂ = 0) (i : τ) :
    MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.subst ![u₁, u₂] (addSeries W)) =
      MvPowerSeries.coeff (Finsupp.single i 1) u₁ + MvPowerSeries.coeff (Finsupp.single i 1) u₂ := by
  rw [coeff_single_subst_pair (two_le_order_addSeries_sub' W) h₁ h₂, one_mul, one_mul]

/- English proof (translation)
The claim follows from `MvPowerSeries.constantCoeff_subst_eq_zero (GroundTheory.LocalField.FormalGroup.hasSubst_pair h₁ h₂) (fun i => by fin_cases i <;> simpa) (constantCoeff_addSeries W)`.
-/
theorem constantCoeff_subst_addSeries {u₁ u₂ : MvPowerSeries τ R}
    (h₁ : MvPowerSeries.constantCoeff u₁ = 0) (h₂ : MvPowerSeries.constantCoeff u₂ = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst ![u₁, u₂] (addSeries W)) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (GroundTheory.LocalField.FormalGroup.hasSubst_pair h₁ h₂)
    (fun i => by fin_cases i <;> simpa) (constantCoeff_addSeries W)

/- English proof (translation)
Establish `hab` using `GroundTheory.LocalField.FormalGroup.hasSubst_pair h₁ h₂`. Rewrite using `[gAt, GroundTheory.LocalField.FormalGroup.subst_powerSeries_subst (PowerSeries.HasSubst.X i) hab, MvPowerSeries.subst_X hab, gAt]`.
-/
theorem subst_pair_gAt {u₁ u₂ : MvPowerSeries τ R} (h₁ : MvPowerSeries.constantCoeff u₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff u₂ = 0) (i : Fin 2) :
    MvPowerSeries.subst ![u₁, u₂] (gAt W (MvPowerSeries.X i)) = gAt W (![u₁, u₂] i) := by
  have hab := GroundTheory.LocalField.FormalGroup.hasSubst_pair h₁ h₂
  rw [gAt, GroundTheory.LocalField.FormalGroup.subst_powerSeries_subst (PowerSeries.HasSubst.X i) hab,
    MvPowerSeries.subst_X hab, gAt]

/- English proof (translation)
Establish `hab` using `GroundTheory.LocalField.FormalGroup.hasSubst_pair h₁ h₂`. Establish `hg : gAt W u₂ - gAt W u₁ = (u₂ - u₁) * MvPowerSeries.subst ![u₁, u₂] (divDiff (formalG W))`. Use `congrArg (MvPowerSeries.subst ![u₁, u₂]) (gAt_X_one_sub_gAt_X_zero W)` as an intermediate fact. Rewrite `this` using `[MvPowerSeries.subst_sub hab, MvPowerSeries.subst_mul hab, MvPowerSeries.subst_sub hab, MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab, subst_pair_gAt W h₁ h₂, subst_pair_gAt W h₁ h₂]`. Then use the resulting hypothesis. Rewrite using `[wAt_eq_mul_gAt W h₁, wAt_eq_mul_gAt W h₂]`.

Introduce `h`. Establish `: u₁ * u₂ * ((u₂ - u₁) * MvPowerSeries.subst ![u₁, u₂] (divDiff (formalG W))) = 0`. Rewrite using `[← hg]`. Take the linear combination `h`. Simplify using `only [mul_eq_zero, hu₁, hu₂, hD, sub_eq_zero, false_or, or_false] at this`.

Conclude with `h12 this.symm`.
-/
theorem mul_wAt_ne [IsDomain R] {u₁ u₂ : MvPowerSeries τ R}
    (h₁ : MvPowerSeries.constantCoeff u₁ = 0) (h₂ : MvPowerSeries.constantCoeff u₂ = 0)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (h12 : u₁ ≠ u₂)
    (hD : MvPowerSeries.subst ![u₁, u₂] (divDiff (formalG W)) ≠ 0) :
    u₁ * wAt W u₂ ≠ u₂ * wAt W u₁ := by
  have hab := GroundTheory.LocalField.FormalGroup.hasSubst_pair h₁ h₂
  have hg : gAt W u₂ - gAt W u₁ = (u₂ - u₁) * MvPowerSeries.subst ![u₁, u₂] (divDiff (formalG W)) := by
    have := congrArg (MvPowerSeries.subst ![u₁, u₂]) (gAt_X_one_sub_gAt_X_zero W)
    rwa [MvPowerSeries.subst_sub hab, MvPowerSeries.subst_mul hab, MvPowerSeries.subst_sub hab,
      MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab, subst_pair_gAt W h₁ h₂,
      subst_pair_gAt W h₁ h₂] at this
  rw [wAt_eq_mul_gAt W h₁, wAt_eq_mul_gAt W h₂]
  intro h
  have : u₁ * u₂ * ((u₂ - u₁) * MvPowerSeries.subst ![u₁, u₂] (divDiff (formalG W))) = 0 := by
    rw [← hg]; linear_combination h
  simp only [mul_eq_zero, hu₁, hu₂, hD, sub_eq_zero, false_or, or_false] at this
  exact h12 this.symm

/- English proof (translation)
Introduce and unpack `rfl`. Simplify using `at h`.
-/
theorem ne_zero_of_coeff_ne_zero {f : MvPowerSeries τ R} {d : τ →₀ ℕ}
    (h : MvPowerSeries.coeff d f ≠ 0) : f ≠ 0 := by
  rintro rfl; simp at h

end Lin

section Assoc

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R) [Fact (W.Δ ≠ 0)]

attribute [local instance] isDomain_mvPowerSeries

open Classical in

/- English proof (translation)
Establish `hu₁` using `ne_zero_of_coeff_ne_zero hi₁`. Establish `hu₂` using `ne_zero_of_coeff_ne_zero hi₂`. Establish `h12 : u₁ ≠ u₂` using `fun h => hi₃ (by rw [h])`. Establish `hD : MvPowerSeries.subst ![u₁, u₂] (divDiff (formalG W)) ≠ 0`. Use `ne_zero_of_coeff_ne_zero (d := Finsupp.single i₄ 1) ?_` and prove the remaining obligations.

Rewrite using `[coeff_single_subst_pair (two_le_order_divDiff_formalG W) h₁ h₂, one_mul, one_mul]`. Conclude with `hi₄`. Conclude with `pointOf_add W τ h₁ h₂ hu₁ hu₂ (mul_wAt_ne W h₁ h₂ hu₁ hu₂ h12 hD)`.
-/
theorem pointOf_add_of_coeff {τ : Type*} [Nonempty τ] {u₁ u₂ : MvPowerSeries τ R}
    (h₁ : MvPowerSeries.constantCoeff u₁ = 0) (h₂ : MvPowerSeries.constantCoeff u₂ = 0)
    {i₁ i₂ i₃ i₄ : τ} (hi₁ : MvPowerSeries.coeff (Finsupp.single i₁ 1) u₁ ≠ 0)
    (hi₂ : MvPowerSeries.coeff (Finsupp.single i₂ 1) u₂ ≠ 0)
    (hi₃ : MvPowerSeries.coeff (Finsupp.single i₃ 1) u₁ ≠
      MvPowerSeries.coeff (Finsupp.single i₃ 1) u₂)
    (hi₄ : MvPowerSeries.coeff (Finsupp.single i₄ 1) u₁ +
      MvPowerSeries.coeff (Finsupp.single i₄ 1) u₂ ≠ 0) :
    pointOf W τ u₁ + pointOf W τ u₂ =
      pointOf W τ (MvPowerSeries.subst ![u₁, u₂] (addSeries W)) := by
  have hu₁ := ne_zero_of_coeff_ne_zero hi₁
  have hu₂ := ne_zero_of_coeff_ne_zero hi₂
  have h12 : u₁ ≠ u₂ := fun h => hi₃ (by rw [h])
  have hD : MvPowerSeries.subst ![u₁, u₂] (divDiff (formalG W)) ≠ 0 := by
    refine ne_zero_of_coeff_ne_zero (d := Finsupp.single i₄ 1) ?_
    rw [coeff_single_subst_pair (two_le_order_divDiff_formalG W) h₁ h₂, one_mul, one_mul]
    exact hi₄
  exact pointOf_add W τ h₁ h₂ hu₁ hu₂ (mul_wAt_ne W h₁ h₂ hu₁ hu₂ h12 hD)

/- English proof (translation)
Use `set Y : Fin 3 → MvPowerSeries (Fin 3) R := MvPowerSeries.X with hY`. Establish `hc : ∀ i, MvPowerSeries.constantCoeff (Y i) = 0` using `fun i => by simp [hY]`. Establish `hA` using `constantCoeff_subst_addSeries W (hc 0) (hc 1)`. Establish `hB` using `constantCoeff_subst_addSeries W (hc 1) (hc 2)`. Establish `lA : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.subst ![Y 0, Y 1] (addSeries W)) = (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0)` using `fun i => by`.

Rewrite using `[coeff_single_subst_addSeries W (hc 0) (hc 1), hY, coeff_single_X, coeff_single_X]`. Establish `lB : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.subst ![Y 1, Y 2] (addSeries W)) = (if i = 1 then 1 else 0) + (if i = 2 then 1 else 0)` using `fun i => by`. Rewrite using `[coeff_single_subst_addSeries W (hc 1) (hc 2), hY, coeff_single_X, coeff_single_X]`. Establish `lY : ∀ i j, MvPowerSeries.coeff (Finsupp.single i 1) (Y j) = if i = j then 1 else 0` using `fun i j => by rw [hY, coeff_single_X]`. Establish `e01` using `pointOf_add_of_coeff W (hc 0) (hc 1) (i₁ := 0) (i₂ := 1) (i₃ := 0) (i₄ := 0) (by simp [lY]) (by simp [lY]) (by simp [lY]) (by simp [lY])`.

Establish `e12` using `pointOf_add_of_coeff W (hc 1) (hc 2) (i₁ := 1) (i₂ := 2) (i₃ := 1) (i₄ := 1) (by simp [lY]) (by simp [lY]) (by simp [lY]) (by simp [lY])`. Establish `eL` using `pointOf_add_of_coeff W hA (hc 2) (i₁ := 0) (i₂ := 2) (i₃ := 0) (i₄ := 0) (by simp [lA]) (by simp [lY]) (by simp [lA, lY]) (by simp [lA, lY])`. Establish `eR` using `pointOf_add_of_coeff W (hc 0) hB (i₁ := 0) (i₂ := 1) (i₃ := 0) (i₄ := 0) (by simp [lY]) (by simp [lB]) (by simp [lB, lY]) (by simp [lB, lY])`. Establish `hL` using `constantCoeff_subst_addSeries W hA (hc 2)`. Establish `hR` using `constantCoeff_subst_addSeries W (hc 0) hB`.

Use `pointOf_injective W (Fin 3) hL hR ?_ ?_ ?_` and prove the remaining obligations. Use `ne_zero_of_coeff_ne_zero (d := Finsupp.single 0 1) ?_` and prove the remaining obligations. Rewrite using `[coeff_single_subst_addSeries W hA (hc 2), lA, lY]`. Simplify using the standard rewrite rules. Use `ne_zero_of_coeff_ne_zero (d := Finsupp.single 0 1) ?_` and prove the remaining obligations.

Rewrite using `[coeff_single_subst_addSeries W (hc 0) hB, lB, lY]`. Simplify using the standard rewrite rules. Rewrite using `[← eL, ← eR, ← e01, ← e12, add_assoc]`.
-/
theorem addSeries_assoc_of_isDomain :
    MvPowerSeries.subst ![MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 1] (addSeries W), MvPowerSeries.X 2] (addSeries W) =
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 2] (addSeries W)]
      (addSeries W) := by
  classical
  set Y : Fin 3 → MvPowerSeries (Fin 3) R := MvPowerSeries.X with hY
  have hc : ∀ i, MvPowerSeries.constantCoeff (Y i) = 0 := fun i => by simp [hY]
  have hA := constantCoeff_subst_addSeries W (hc 0) (hc 1)
  have hB := constantCoeff_subst_addSeries W (hc 1) (hc 2)
  have lA : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1)
      (MvPowerSeries.subst ![Y 0, Y 1] (addSeries W)) = (if i = 0 then 1 else 0) +
        (if i = 1 then 1 else 0) := fun i => by
    rw [coeff_single_subst_addSeries W (hc 0) (hc 1), hY, coeff_single_X, coeff_single_X]
  have lB : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1)
      (MvPowerSeries.subst ![Y 1, Y 2] (addSeries W)) = (if i = 1 then 1 else 0) +
        (if i = 2 then 1 else 0) := fun i => by
    rw [coeff_single_subst_addSeries W (hc 1) (hc 2), hY, coeff_single_X, coeff_single_X]
  have lY : ∀ i j, MvPowerSeries.coeff (Finsupp.single i 1) (Y j) = if i = j then 1 else 0 :=
    fun i j => by rw [hY, coeff_single_X]
  have e01 := pointOf_add_of_coeff W (hc 0) (hc 1) (i₁ := 0) (i₂ := 1) (i₃ := 0) (i₄ := 0)
    (by simp [lY]) (by simp [lY]) (by simp [lY]) (by simp [lY])
  have e12 := pointOf_add_of_coeff W (hc 1) (hc 2) (i₁ := 1) (i₂ := 2) (i₃ := 1) (i₄ := 1)
    (by simp [lY]) (by simp [lY]) (by simp [lY]) (by simp [lY])
  have eL := pointOf_add_of_coeff W hA (hc 2) (i₁ := 0) (i₂ := 2) (i₃ := 0) (i₄ := 0)
    (by simp [lA]) (by simp [lY]) (by simp [lA, lY]) (by simp [lA, lY])
  have eR := pointOf_add_of_coeff W (hc 0) hB (i₁ := 0) (i₂ := 1) (i₃ := 0) (i₄ := 0)
    (by simp [lY]) (by simp [lB]) (by simp [lB, lY]) (by simp [lB, lY])
  have hL := constantCoeff_subst_addSeries W hA (hc 2)
  have hR := constantCoeff_subst_addSeries W (hc 0) hB
  refine pointOf_injective W (Fin 3) hL hR ?_ ?_ ?_
  · refine ne_zero_of_coeff_ne_zero (d := Finsupp.single 0 1) ?_
    rw [coeff_single_subst_addSeries W hA (hc 2), lA, lY]; simp
  · refine ne_zero_of_coeff_ne_zero (d := Finsupp.single 0 1) ?_
    rw [coeff_single_subst_addSeries W (hc 0) hB, lB, lY]; simp
  · rw [← eL, ← eR, ← e01, ← e12, add_assoc]

/- English proof (translation)
Establish `hc : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) = 0` using `fun i => by simp`. Establish `lY : ∀ i j : Fin 2, MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.X j : MvPowerSeries (Fin 2) R) = if i = j then 1 else 0` using `fun i j => coeff_single_X i j`. Establish `e01` using `pointOf_add_of_coeff W (hc 0) (hc 1) (i₁ := 0) (i₂ := 1) (i₃ := 0) (i₄ := 0) (by simp [lY]) (by simp [lY]) (by simp [lY]) (by simp [lY])`. Establish `e10` using `pointOf_add_of_coeff W (hc 1) (hc 0) (i₁ := 1) (i₂ := 0) (i₃ := 0) (i₄ := 0) (by simp [lY]) (by simp [lY]) (by simp [lY]) (by simp [lY])`. Rewrite `e01` using `[GroundTheory.LocalField.FormalGroup.subst_X_X]`.

Establish `h01` using `constantCoeff_addSeries W`. Establish `h10` using `constantCoeff_subst_addSeries W (hc 1) (hc 0)`. Use `pointOf_injective W (Fin 2) h01 h10 ?_ ?_ ?_` and prove the remaining obligations. Use `ne_zero_of_coeff_ne_zero (d := Finsupp.single 0 1) ?_` and prove the remaining obligations. Use `coeff_single_subst_addSeries W (hc 0) (hc 1) 0` as an intermediate fact.

Rewrite `this` using `[GroundTheory.LocalField.FormalGroup.subst_X_X]`. Rewrite using `[this, lY, lY]`. Simplify using the standard rewrite rules. Use `ne_zero_of_coeff_ne_zero (d := Finsupp.single 0 1) ?_` and prove the remaining obligations. Rewrite using `[coeff_single_subst_addSeries W (hc 1) (hc 0), lY, lY]`.

Simplify using the standard rewrite rules. Rewrite using `[← e01, ← e10, add_comm]`.
-/
theorem addSeries_comm_of_isDomain :
    addSeries W = MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (addSeries W) := by
  classical
  have hc : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) = 0 :=
    fun i => by simp
  have lY : ∀ i j : Fin 2, MvPowerSeries.coeff (Finsupp.single i 1)
      (MvPowerSeries.X j : MvPowerSeries (Fin 2) R) = if i = j then 1 else 0 :=
    fun i j => coeff_single_X i j
  have e01 := pointOf_add_of_coeff W (hc 0) (hc 1) (i₁ := 0) (i₂ := 1) (i₃ := 0) (i₄ := 0)
    (by simp [lY]) (by simp [lY]) (by simp [lY]) (by simp [lY])
  have e10 := pointOf_add_of_coeff W (hc 1) (hc 0) (i₁ := 1) (i₂ := 0) (i₃ := 0) (i₄ := 0)
    (by simp [lY]) (by simp [lY]) (by simp [lY]) (by simp [lY])
  rw [GroundTheory.LocalField.FormalGroup.subst_X_X] at e01
  have h01 := constantCoeff_addSeries W
  have h10 := constantCoeff_subst_addSeries W (hc 1) (hc 0)
  refine pointOf_injective W (Fin 2) h01 h10 ?_ ?_ ?_
  · refine ne_zero_of_coeff_ne_zero (d := Finsupp.single 0 1) ?_
    have := coeff_single_subst_addSeries W (hc 0) (hc 1) 0
    rw [GroundTheory.LocalField.FormalGroup.subst_X_X] at this
    rw [this, lY, lY]; simp
  · refine ne_zero_of_coeff_ne_zero (d := Finsupp.single 0 1) ?_
    rw [coeff_single_subst_addSeries W (hc 1) (hc 0), lY, lY]; simp
  · rw [← e01, ← e10, add_comm]

end Assoc

section FormalGroupLaw

def univCurve : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

/- English proof (translation)
Introduce `h`. Establish `h'` using `congrArg (MvPolynomial.eval ![(0 : ℤ), 0, 1, 0, 0]) h`. Rewrite `h'` using `[← WeierstrassCurve.map_Δ, map_zero]`. Establish `e : univCurve.map (MvPolynomial.eval ![(0 : ℤ), 0, 1, 0, 0]) = ⟨0, 0, 1, 0, 0⟩`. Apply the tactic sequence `ext <;> simp [univCurve]`.

Rewrite `h'` using `[e]`. Evaluate the numerical expressions using `[WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈] at h'`.
-/
theorem univCurve_Δ_ne_zero : univCurve.Δ ≠ 0 := by
  intro h
  have h' := congrArg (MvPolynomial.eval ![(0 : ℤ), 0, 1, 0, 0]) h
  rw [← WeierstrassCurve.map_Δ, map_zero] at h'
  have e : univCurve.map (MvPolynomial.eval ![(0 : ℤ), 0, 1, 0, 0]) = ⟨0, 0, 1, 0, 0⟩ := by
    ext <;> simp [univCurve]
  rw [e] at h'
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈] at h'

instance : Fact (univCurve.Δ ≠ 0) := ⟨univCurve_Δ_ne_zero⟩

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def univMap : MvPolynomial (Fin 5) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [univCurve, univMap]`.
-/
theorem univCurve_map : univCurve.map (univMap W) = W := by
  ext <;> simp [univCurve, univMap]

/- English proof (translation)
Rewrite using `[map_addSeries, univCurve_map]`.
-/
theorem addSeries_eq_map : addSeries W = MvPowerSeries.map (univMap W) (addSeries univCurve) := by
  rw [map_addSeries, univCurve_map]

/- English proof (translation)
Establish `h` using `MvPowerSeries.coeff_of_lt_order (d := Finsupp.single i 1) (lt_of_lt_of_le (by simp) (two_le_order_addSeries_sub W))`. Rewrite `h` using `[map_sub, sub_eq_zero]`. Rewrite using `[h, map_add, coeff_single_X, coeff_single_X]`. Apply the tactic sequence `fin_cases i <;> simp`.
-/
theorem coeff_single_addSeries (i : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single i 1) (addSeries W) = 1 := by
  classical
  have h := MvPowerSeries.coeff_of_lt_order (d := Finsupp.single i 1)
    (lt_of_lt_of_le (by simp) (two_le_order_addSeries_sub W))
  rw [map_sub, sub_eq_zero] at h
  rw [h, map_add, coeff_single_X, coeff_single_X]
  fin_cases i <;> simp

def univFormalGroup : FormalGroup (MvPolynomial (Fin 5) ℤ) where
  toPowerSeries := addSeries univCurve
  zero_constantCoeff := constantCoeff_addSeries _
  lin_coeff_X := coeff_single_addSeries _ 0
  lin_coeff_Y := coeff_single_addSeries _ 1
  assoc := addSeries_assoc_of_isDomain univCurve

def formalGroup : FormalGroup R where
  toPowerSeries := addSeries W
  zero_constantCoeff := constantCoeff_addSeries W
  lin_coeff_X := coeff_single_addSeries W 0
  lin_coeff_Y := coeff_single_addSeries W 1
  assoc := by
    have := (univFormalGroup.map (univMap W)).assoc
    rwa [FormalGroup.map_toPowerSeries, univFormalGroup, ← addSeries_eq_map] at this

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem formalGroup_toPowerSeries : (formalGroup W).toPowerSeries = addSeries W := rfl

instance : (formalGroup W).IsComm where
  comm := by
    change addSeries W = MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (addSeries W)
    have hs : MvPowerSeries.HasSubst
        ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (MvPolynomial (Fin 5) ℤ)), MvPowerSeries.X 0] :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp
    conv_lhs => rw [addSeries_eq_map, addSeries_comm_of_isDomain univCurve]
    rw [MvPowerSeries.map_subst hs, ← addSeries_eq_map]
    congr 1
    funext i
    fin_cases i <;> simp

/- English proof (translation)
Use `ext1`. Simplify using `[map_addSeries]`.
-/
theorem formalGroup_map {S : Type*} [CommRing S] (f : R →+* S) :
    (formalGroup W).map f = formalGroup (W.map f) := by
  ext1
  simp [map_addSeries]

end FormalGroupLaw

end

end GroundTheory.Arith.Abelian
