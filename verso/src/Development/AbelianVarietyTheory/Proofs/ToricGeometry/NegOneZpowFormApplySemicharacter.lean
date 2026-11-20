import Mathlib

open Matrix Polynomial
open scoped BigOperators

namespace GlobalTheory

/- English proof (translation)
Introduce `X _ E w w' halt hsum hadj x y`. Establish `hskew : ∀ a b, E a b = - E b a`. Introduce `a b`. Establish `h` using `halt (a + b)`. Simplify using `only [map_add, LinearMap.add_apply, halt] at h`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hy : w y + w' y = y`. Use `LinearMap.congr_fun hsum y` as an intermediate fact. Simplify using `using this`. Establish `h1 : E x (w y) + E x (w' y) = E x y` using `by rw [← map_add, hy]`.

Establish `h2 : E y (w x) = - E x (w' y)` using `by rw [hskew, hadj]`. Establish `h3 : E (x + y) (w (x + y)) = E x (w x) + E y (w y) + E x y + 2 * (E x (w y) - E x y)`. Simplify using `only [map_add, LinearMap.add_apply]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hne : (-1 : ℂ) ≠ 0` using `by norm_num`.

Rewrite using `[h3, zpow_add₀ hne, zpow_add₀ hne, zpow_add₀ hne, _root_.zpow_mul]`. Establish `h4 : (-1 : ℂ) ^ (2 : ℤ) = 1` using `by norm_num`. Rewrite using `[h4, _root_.one_zpow, mul_one]`.
-/
theorem neg_one_zpow_form_apply_semicharacter :
    (∀ (X : Type) [AddCommGroup X] (E : LinearMap.BilinForm ℤ X) (w w' : X →ₗ[ℤ] X), (∀ x, E x x = 0) → w + w' = LinearMap.id → (∀ x y, E (w x) y = E x (w' y)) → ∀ x y, (-1 : ℂ) ^ E (x + y) (w (x + y)) = (-1) ^ E x (w x) * (-1) ^ E y (w y) * (-1) ^ E x y) := by
  intro X _ E w w' halt hsum hadj x y
  have hskew : ∀ a b, E a b = - E b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add, LinearMap.add_apply, halt] at h
    linarith
  have hy : w y + w' y = y := by
    have := LinearMap.congr_fun hsum y
    simpa using this
  have h1 : E x (w y) + E x (w' y) = E x y := by rw [← map_add, hy]
  have h2 : E y (w x) = - E x (w' y) := by rw [hskew, hadj]
  have h3 : E (x + y) (w (x + y))
      = E x (w x) + E y (w y) + E x y + 2 * (E x (w y) - E x y) := by
    simp only [map_add, LinearMap.add_apply]
    linarith
  have hne : (-1 : ℂ) ≠ 0 := by norm_num
  rw [h3, zpow_add₀ hne, zpow_add₀ hne, zpow_add₀ hne, _root_.zpow_mul]
  have h4 : (-1 : ℂ) ^ (2 : ℤ) = 1 := by norm_num
  rw [h4, _root_.one_zpow, mul_one]

end GlobalTheory
