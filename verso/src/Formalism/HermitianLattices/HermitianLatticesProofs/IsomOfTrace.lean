import Mathlib
import Formalism.HermitianLattices.DefsCS

open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

/- English proof (translation)
Introduce `K V _ _ _ _ _ h g hg`. Use `show ∀ x y, h (g x) (g y) = h x y`. Introduce `x y`. Assume the negation of the conclusion as `hne`. Establish `hd : h (g x) (g y) - h x y ≠ 0` using `sub_ne_zero.mpr hne`.

Establish `key` using `hg x ((h (g x) (g y) - h x y)⁻¹ • y)`. Simplify using `only [map_smul, smul_eq_mul] at key`. Establish `h0 : Algebra.trace ℚ K ((h (g x) (g y) - h x y)⁻¹ * (h (g x) (g y) - h x y)) = 0`. Rewrite using `[mul_sub, map_sub, key, sub_self]`. Rewrite `h0` using `[inv_mul_cancel₀ hd]`.

Establish `h1 : Algebra.trace ℚ K (1 : K) = (Module.finrank ℚ K : ℚ)`. Rewrite using `[← map_one (algebraMap ℚ K), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]`. Rewrite `h0` using `[h1]`. Establish `hpos : 0 < Module.finrank ℚ K` using `Module.finrank_pos`. Conclude with `absurd h0 (by exact_mod_cast hpos.ne')`.
-/
theorem isomOfTrace : IsomOfTrace := by
  intro K V _ _ _ _ _ h g hg
  show ∀ x y, h (g x) (g y) = h x y
  intro x y
  by_contra hne
  have hd : h (g x) (g y) - h x y ≠ 0 := sub_ne_zero.mpr hne
  have key := hg x ((h (g x) (g y) - h x y)⁻¹ • y)
  simp only [map_smul, smul_eq_mul] at key
  have h0 : Algebra.trace ℚ K ((h (g x) (g y) - h x y)⁻¹ * (h (g x) (g y) - h x y)) = 0 := by
    rw [mul_sub, map_sub, key, sub_self]
  rw [inv_mul_cancel₀ hd] at h0
  have h1 : Algebra.trace ℚ K (1 : K) = (Module.finrank ℚ K : ℚ) := by
    rw [← map_one (algebraMap ℚ K), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
  rw [h1] at h0
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  exact absurd h0 (by exact_mod_cast hpos.ne')

end Formalism.HermitianLatticesTheory
