import Mathlib

namespace Bl.SecondBlockLemmaO

/- English proof (translation)
Introduce `V _ _ _ ϖ hϖ`. Establish `hϖ0 : ϖ ≠ 0` using `hϖ.ne_zero`. Establish `hinj` using `IsFractionRing.injective V (FractionRing V)`. Use `(isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨_, n, rfl⟩`.

Rewrite using `[isUnit_iff_ne_zero]`. Conclude with `(map_ne_zero_iff _ hinj).2 (pow_ne_zero n hϖ0)`. Introduce `z`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := V) z`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`.

Establish `hbK : algebraMap V (FractionRing V) b ≠ 0` using `(map_ne_zero_iff _ hinj).2 hb0`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ`. Use `⟨⟨a * ↑u⁻¹, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Establish `hu' : algebraMap V (FractionRing V) (↑u⁻¹ : V) * algebraMap V (FractionRing V) (↑u : V) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`.

Use `show algebraMap V (FractionRing V) a / algebraMap V (FractionRing V) b * algebraMap V (FractionRing V) (ϖ ^ n) = algebraMap V (FractionRing V) (a * ↑u⁻¹)`. Rewrite using `[div_mul_eq_mul_div, div_eq_iff hbK, hu]`. Simplify using `only [map_mul, map_pow]`. Take the linear combination `(-(algebraMap V (FractionRing V) a * algebraMap V (FractionRing V) ϖ ^ n)) * hu'`. Introduce `x y h`.

Conclude with `⟨1, by rw [hinj h]⟩`.
-/
theorem goal1 :
  ∀ {V : Type} [inst : CommRing.{0} V] [inst_1 : IsDomain.{0} V] [IsDiscreteValuationRing.{0} V] {ϖ : V},
  Irreducible.{0} ϖ → IsLocalization.Away.{0, 0} ϖ (FractionRing.{0} V) := by
  intro V _ _ _ ϖ hϖ
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hinj := IsFractionRing.injective V (FractionRing V)
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ hinj).2 (pow_ne_zero n hϖ0)
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) z
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap V (FractionRing V) b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    refine ⟨⟨a * ↑u⁻¹, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
    have hu' : algebraMap V (FractionRing V) (↑u⁻¹ : V) * algebraMap V (FractionRing V) (↑u : V) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    show algebraMap V (FractionRing V) a / algebraMap V (FractionRing V) b *
      algebraMap V (FractionRing V) (ϖ ^ n) = algebraMap V (FractionRing V) (a * ↑u⁻¹)
    rw [div_mul_eq_mul_div, div_eq_iff hbK, hu]
    simp only [map_mul, map_pow]
    linear_combination (-(algebraMap V (FractionRing V) a * algebraMap V (FractionRing V) ϖ ^ n)) * hu'
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

end Bl.SecondBlockLemmaO
