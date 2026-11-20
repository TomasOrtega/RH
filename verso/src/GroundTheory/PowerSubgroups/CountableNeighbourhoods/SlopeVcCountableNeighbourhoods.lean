import Mathlib

namespace GroundTheory.Variant₂.N1

open WeierstrassCurve

def vcX {R : Type*} [CommRing R] (C : WeierstrassCurve.VariableChange R) (x : R) : R :=
  ↑C.u⁻¹ ^ 2 * (x - C.r)

def vcY {R : Type*} [CommRing R] (C : WeierstrassCurve.VariableChange R) (x y : R) : R :=
  ↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)

/- English proof (translation)
Establish `hv : (↑C.u⁻¹ : F) ≠ 0` using `Units.ne_zero _`. Distinguish the cases in `hx : x₁ = x₂`. Substitute `hx` using the available equality. Establish `hy : y₁ ≠ W.toAffine.negY x₁ y₂` using `fun h => hxy ⟨rfl, h⟩`. Establish `hyy : y₁ = y₂` using `Affine.Y_eq_of_Y_ne h₁ h₂ rfl hy`.

Substitute `hyy` using the available equality. Establish `key : vcY C x₁ y₁ - (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) = (↑C.u⁻¹ : F) ^ 3 * (y₁ - W.toAffine.negY x₁ y₁)`. Simplify using `only [vcX, vcY, Affine.negY, variableChange_a₁, variableChange_a₃]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd : y₁ - W.toAffine.negY x₁ y₁ ≠ 0` using `sub_ne_zero.mpr hy`.

Establish `hd' : vcY C x₁ y₁ - (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) ≠ 0`. Rewrite using `[key]`. Conclude with `mul_ne_zero (pow_ne_zero _ hv) hd`. Establish `hy' : vcY C x₁ y₁ ≠ (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁)` using `sub_ne_zero.mp hd'`. Rewrite using `[Affine.slope_of_Y_ne rfl hy, Affine.slope_of_Y_ne rfl hy', key]`.

Establish `num : 3 * vcX C x₁ ^ 2 + 2 * (C • W).toAffine.a₂ * vcX C x₁ + (C • W).toAffine.a₄ - (C • W).toAffine.a₁ * vcY C x₁ y₁ = (↑C.u⁻¹ : F) ^ 4 * ((3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁) - C.s * (y₁ - W.toAffine.negY x₁ y₁))`. Simplify using `only [vcX, vcY, Affine.negY, variableChange_a₁, variableChange_a₂, variableChange_a₄]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[num]`. Use `set D := y₁ - W.toAffine.negY x₁ y₁`.

Use `set N := 3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁`. Clear the denominators using the available nonvanishing facts. Establish `hX : vcX C x₁ ≠ vcX C x₂`. Introduce `h`. Apply `hx` to reduce the goal to its premises.

Simplify using `only [vcX] at h`. Use `mul_left_cancel₀ (pow_ne_zero 2 hv) h` as an intermediate fact. Conclude with `sub_left_injective this`. Rewrite using `[Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hX]`. Establish `hd : x₁ - x₂ ≠ 0` using `sub_ne_zero.mpr hx`.

Establish `hXd : vcX C x₁ - vcX C x₂ = (↑C.u⁻¹ : F) ^ 2 * (x₁ - x₂)`. Simplify using `only [vcX]`. Expand and normalize the polynomial expressions, which then agree. Establish `hYd : vcY C x₁ y₁ - vcY C x₂ y₂ = (↑C.u⁻¹ : F) ^ 3 * ((y₁ - y₂) - C.s * (x₁ - x₂))`. Simplify using `only [vcY]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hXd, hYd]`. Clear the denominators using the available nonvanishing facts.
-/
theorem slope_variableChange {F : Type*} [Field F] (C : WeierstrassCurve.VariableChange F)
    (W : WeierstrassCurve F) [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) (vcY C x₂ y₂) =
      ↑C.u⁻¹ * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) := by
  have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ W.toAffine.negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩
    have hyy : y₁ = y₂ := Affine.Y_eq_of_Y_ne h₁ h₂ rfl hy
    subst hyy
    have key : vcY C x₁ y₁ - (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) =
        (↑C.u⁻¹ : F) ^ 3 * (y₁ - W.toAffine.negY x₁ y₁) := by
      simp only [vcX, vcY, Affine.negY, variableChange_a₁, variableChange_a₃]
      ring
    have hd : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    have hd' : vcY C x₁ y₁ - (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) ≠ 0 := by
      rw [key]; exact mul_ne_zero (pow_ne_zero _ hv) hd
    have hy' : vcY C x₁ y₁ ≠ (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) :=
      sub_ne_zero.mp hd'
    rw [Affine.slope_of_Y_ne rfl hy, Affine.slope_of_Y_ne rfl hy', key]
    have num : 3 * vcX C x₁ ^ 2 + 2 * (C • W).toAffine.a₂ * vcX C x₁ + (C • W).toAffine.a₄ -
        (C • W).toAffine.a₁ * vcY C x₁ y₁ =
        (↑C.u⁻¹ : F) ^ 4 * ((3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ -
          W.toAffine.a₁ * y₁) - C.s * (y₁ - W.toAffine.negY x₁ y₁)) := by
      simp only [vcX, vcY, Affine.negY, variableChange_a₁, variableChange_a₂, variableChange_a₄]
      ring
    rw [num]
    set D := y₁ - W.toAffine.negY x₁ y₁
    set N := 3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁
    field_simp
  · have hX : vcX C x₁ ≠ vcX C x₂ := by
      intro h
      apply hx
      simp only [vcX] at h
      have := mul_left_cancel₀ (pow_ne_zero 2 hv) h
      exact sub_left_injective this
    rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hX]
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hXd : vcX C x₁ - vcX C x₂ = (↑C.u⁻¹ : F) ^ 2 * (x₁ - x₂) := by
      simp only [vcX]; ring
    have hYd : vcY C x₁ y₁ - vcY C x₂ y₂ =
        (↑C.u⁻¹ : F) ^ 3 * ((y₁ - y₂) - C.s * (x₁ - x₂)) := by
      simp only [vcY]; ring
    rw [hXd, hYd]
    field_simp

end GroundTheory.Variant₂.N1
