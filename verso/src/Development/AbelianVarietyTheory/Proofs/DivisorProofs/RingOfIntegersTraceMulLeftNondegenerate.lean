import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ x hx`. Assume the negation of the conclusion as `hne`. Establish `hxK : (x : K) ≠ 0`. Introduce `h`. Conclude with `hne (RingOfIntegers.coe_eq_zero_iff.mp h)`.

Establish `halg : IsAlgebraic ℤ ((x : K)⁻¹)` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic _)`. Take `⟨d, hd0, hdi⟩` from `halg.exists_integral_multiple`. Set `y : 𝓞 K` to `⟨d • (x : K)⁻¹, hdi⟩`. Establish `hxy : x * y = algebraMap ℤ (𝓞 K) d`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Use `show (x : K) * (d • (x : K)⁻¹) = ((algebraMap ℤ (𝓞 K) d : 𝓞 K) : K)`. Rewrite using `[eq_intCast, zsmul_eq_mul]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `first | exact (map_intCast (algebraMap (𝓞 K) K) d).symm | norm_cast | simp`.

Establish `h` using `hx y`. Rewrite `h` using `[hxy]`. Establish `h2 : LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (algebraMap ℤ (𝓞 K) d)) = Algebra.trace ℤ (𝓞 K) (algebraMap ℤ (𝓞 K) d)`. Rewrite using `[Algebra.trace_apply]`. Both sides reduce to the same expression.

Rewrite `h` using `[h2, Algebra.trace_algebraMap]`. Establish `hpos : 0 < Module.finrank ℤ (𝓞 K)` using `Module.finrank_pos`. Rewrite `h` using `[nsmul_eq_mul]`. Break down `mul_eq_zero.mp h with h | h` into its components or cases. Conclude with `absurd (by exact_mod_cast h) hpos.ne'`.

Conclude with `hd0 h`.
-/
theorem ringOfIntegers_trace_mulLeft_nondegenerate :
    ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K),
      (∀ y : 𝓞 K, LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  intro K _ _ x hx
  by_contra hne
  have hxK : (x : K) ≠ 0 := by
    intro h; exact hne (RingOfIntegers.coe_eq_zero_iff.mp h)
  have halg : IsAlgebraic ℤ ((x : K)⁻¹) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨d, hd0, hdi⟩ := halg.exists_integral_multiple
  let y : 𝓞 K := ⟨d • (x : K)⁻¹, hdi⟩
  have hxy : x * y = algebraMap ℤ (𝓞 K) d := by
    apply RingOfIntegers.coe_injective
    show (x : K) * (d • (x : K)⁻¹) = ((algebraMap ℤ (𝓞 K) d : 𝓞 K) : K)
    rw [eq_intCast, zsmul_eq_mul]
    push_cast
    field_simp
    first | exact (map_intCast (algebraMap (𝓞 K) K) d).symm | norm_cast | simp
  have h := hx y
  rw [hxy] at h
  have h2 : LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (algebraMap ℤ (𝓞 K) d))
      = Algebra.trace ℤ (𝓞 K) (algebraMap ℤ (𝓞 K) d) := by
    rw [Algebra.trace_apply]; rfl
  rw [h2, Algebra.trace_algebraMap] at h
  have hpos : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (by exact_mod_cast h) hpos.ne'
  · exact hd0 h

end GlobalTheory
