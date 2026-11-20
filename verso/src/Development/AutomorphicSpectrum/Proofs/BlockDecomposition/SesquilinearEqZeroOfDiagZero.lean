import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.Sesquilinear

/- English proof (translation)
Use extensionality with `v w`. Establish `h1` using `h (v + w)`. Establish `h2` using `h (v + Complex.I • w)`. Simplify using `only [map_add, LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, h v, h w, smul_eq_mul, zero_add, add_zero, Complex.conj_I, RingHom.id_apply, mul_zero] at h1 h2`. Establish `h3 : B v w = B w v`.

Establish `: Complex.I * (B w v - B v w) = 0` using `by linear_combination h2`. Break down `mul_eq_zero.mp this with h4 | h4` into its components or cases. Conclude with `absurd h4 Complex.I_ne_zero`. Conclude with `(sub_eq_zero.mp h4).symm`. Establish `h5 : (2 : ℂ) * B v w = 0` using `by linear_combination h1 + h3`.

Simplify using `using h5`.
-/
theorem eq_zero_of_diag_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (h : ∀ v, B v v = 0) : B = 0 := by
  ext v w
  have h1 := h (v + w)
  have h2 := h (v + Complex.I • w)
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    h v, h w, smul_eq_mul, zero_add, add_zero, Complex.conj_I, RingHom.id_apply,
    mul_zero] at h1 h2
  have h3 : B v w = B w v := by
    have : Complex.I * (B w v - B v w) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h4 | h4
    · exact absurd h4 Complex.I_ne_zero
    · exact (sub_eq_zero.mp h4).symm
  have h5 : (2 : ℂ) * B v w = 0 := by linear_combination h1 + h3
  simpa using h5

end GlobalTheory.CompanionTheory.Sesquilinear
