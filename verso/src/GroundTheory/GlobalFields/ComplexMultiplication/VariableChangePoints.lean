import Mathlib

namespace GroundTheory.Global

open WeierstrassCurve

variable {F : Type*} [Field F]

section VariableChangePoint

/- English proof (translation)
Rewrite `h`, the goal using `[Affine.nonsingular_iff']`. Take `⟨he, hd⟩` from `h`. Rewrite `he`, the goal using `[Affine.equation_iff']`. Establish `hv : (↑C.u⁻¹ : F) ≠ 0` using `Units.ne_zero _`. Simplify using `only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆]`.

Use `set v : F := ↑C.u⁻¹`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take the linear combination `v ^ 6 * he`. Assume the negation of the conclusion as `hc push Not at hc`. Take `⟨h1, h2⟩` from `hc`.

Establish `hY : 2 * y + W.a₁ * x + W.a₃ = 0`. Establish `: v ^ 3 * (2 * y + W.a₁ * x + W.a₃) = 0` using `by linear_combination h2`. Simplify `this` using `[hv]`. Establish `hX : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0`. Establish `: v ^ 4 * (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) = 0`.

Take the linear combination `h1 - v ^ 4 * C.s * hY`. Simplify `this` using `[hv]`. Break down `hd with hd | hd` into its components or cases. Conclude with `hd hX`. Conclude with `hd hY`.
-/
theorem nonsingular_variableChange (C : VariableChange F) (W : WeierstrassCurve F) {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    (C • W).toAffine.Nonsingular (↑C.u⁻¹ ^ 2 * (x - C.r))
      (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)) := by
  rw [Affine.nonsingular_iff'] at h ⊢
  obtain ⟨he, hd⟩ := h
  rw [Affine.equation_iff'] at he ⊢
  have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆]
  set v : F := ↑C.u⁻¹
  refine ⟨?_, ?_⟩
  · linear_combination v ^ 6 * he
  · by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    have hY : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      have : v ^ 3 * (2 * y + W.a₁ * x + W.a₃) = 0 := by linear_combination h2
      simpa [hv] using this
    have hX : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0 := by
      have : v ^ 4 * (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) = 0 := by
        linear_combination h1 - v ^ 4 * C.s * hY
      simpa [hv] using this
    rcases hd with hd | hd
    · exact hd hX
    · exact hd hY

def variableChangePoint (C : VariableChange F) {W W' : WeierstrassCurve F} (hC : C • W = W') :
    W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (↑C.u⁻¹ ^ 2 * (x - C.r)) (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t))
      (by subst hC; exact nonsingular_variableChange C W h)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem variableChangePoint_zero (C : VariableChange F) {W W' : WeierstrassCurve F}
    (hC : C • W = W') : variableChangePoint C hC .zero = .zero := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem variableChangePoint_some (C : VariableChange F) {W W' : WeierstrassCurve F}
    (hC : C • W = W') {x y : F} (h : W.toAffine.Nonsingular x y) :
    variableChangePoint C hC (.some x y h) =
      .some (↑C.u⁻¹ ^ 2 * (x - C.r)) (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t))
        (by subst hC; exact nonsingular_variableChange C W h) := rfl

end VariableChangePoint

end GroundTheory.Global
