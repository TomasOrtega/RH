import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Anisotropic

namespace PI.Witt

/- English proof (translation)
Unfold `Anisotropic`. Introduce `K V _ _ _ _ _ B hB U hU`. Take `⟨x, hx, y, hy, hxy⟩` from `hU`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `hz : x + star (B x y) • y ∈ U` using `U.add_mem hx (U.smul_mem _ hy)`. Establish `h0` using `hcon _ hz`. Establish `hxx` using `hcon x hx`. Establish `hyy` using `hcon _ (U.smul_mem (star (B x y)) hy)`. Establish `hyx : B y x = star (B x y)` using `(hB x y).symm`.

Establish `e1 : B x (star (B x y) • y) = star (B x y) * B x y`. Rewrite using `[LinearMap.map_smul, smul_eq_mul]`. Establish `e2 : B (star (B x y) • y) x = B x y * star (B x y)`. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star, hyx]`. Establish `e3 : B (x + star (B x y) • y) (x + star (B x y) • y) = B x x + B x (star (B x y) • y) + (B (star (B x y) • y) x + B (star (B x y) • y) (star (B x y) • y))`.

Rewrite using `[LinearMap.map_add₂, map_add, map_add]`. Rewrite `h0` using `[e3, hxx, hyy, e1, e2]`. Establish `h2 : (2 : K) * (B x y * star (B x y)) = 0` using `by linear_combination h0`. Break down `mul_eq_zero.mp h2 with h | h` into its components or cases. Conclude with `two_ne_zero h`.

Break down `mul_eq_zero.mp h with h' | h'` into its components or cases. Conclude with `hxy h'`. Conclude with `hxy (star_eq_zero.mp h')`.
-/
theorem anisotropic' : Anisotropic := by
  unfold Anisotropic
  intro K V _ _ _ _ _ B hB U hU
  obtain ⟨x, hx, y, hy, hxy⟩ := hU
  by_contra hcon
  push_neg at hcon
  have hz : x + star (B x y) • y ∈ U := U.add_mem hx (U.smul_mem _ hy)
  have h0 := hcon _ hz
  have hxx := hcon x hx
  have hyy := hcon _ (U.smul_mem (star (B x y)) hy)
  have hyx : B y x = star (B x y) := (hB x y).symm
  have e1 : B x (star (B x y) • y) = star (B x y) * B x y := by
    rw [LinearMap.map_smul, smul_eq_mul]
  have e2 : B (star (B x y) • y) x = B x y * star (B x y) := by
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star, hyx]
  have e3 : B (x + star (B x y) • y) (x + star (B x y) • y) =
      B x x + B x (star (B x y) • y) + (B (star (B x y) • y) x + B (star (B x y) • y) (star (B x y) • y)) := by
    rw [LinearMap.map_add₂, map_add, map_add]
  rw [e3, hxx, hyy, e1, e2] at h0
  have h2 : (2 : K) * (B x y * star (B x y)) = 0 := by linear_combination h0
  rcases mul_eq_zero.mp h2 with h | h
  · exact two_ne_zero h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hxy h'
    · exact hxy (star_eq_zero.mp h')

end PI.Witt
