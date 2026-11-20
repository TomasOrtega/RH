import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Establish `hτinj : Function.Injective τ`. Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := ℤ)` to reduce the goal to its premises. Use extensionality with `n`. Simplify using `only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]`.

Rewrite using `[eq_intCast, map_intCast]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: ((n : 𝓞 K) : K) = 0` using `by rw [h]; rfl`. Conclude with `this` after adjusting the coercions.

Introduce and unpack `rfl`. Simplify using the standard rewrite rules. Establish `hinj : Function.Injective ((algebraMap (𝓞 K) K).comp τ)` using `(RingOfIntegers.coe_injective (K := K)).comp hτinj`. Set `φ : E →+* K` to `IsFractionRing.lift hinj`. Use `letI : Algebra E K := φ.toAlgebra`.

Establish `hmap : τ = algebraMap (𝓞 E) (𝓞 K)`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `((algebraMap (𝓞 K) K).comp τ) x = φ (algebraMap (𝓞 E) E x)`. Rewrite using `[IsFractionRing.lift_algebraMap]`. Establish `htower` using `Module.finrank_mul_finrank ℚ E K`.

Establish `hE : 0 < Module.finrank ℚ E` using `Module.finrank_pos`. Use `⟨⟨Module.finrank E K, htower.symm⟩, ?_⟩` and prove the remaining obligations. Establish `hq : Module.finrank ℚ K / Module.finrank ℚ E = Module.finrank E K`. Rewrite using `[← htower, Nat.mul_div_cancel_left _ hE]`. Rewrite using `[hq, hmap, Ideal.absNorm_algebraMap (𝓞 E) (𝓞 K) 𝔞, ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 K) K]`.
-/
theorem absNorm_map_ringOfIntegers_hom (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (𝔞 : Ideal (𝓞 E)) :
    Module.finrank ℚ E ∣ Module.finrank ℚ K ∧
      Ideal.absNorm (𝔞.map τ) = Ideal.absNorm 𝔞 ^ (Module.finrank ℚ K / Module.finrank ℚ E) := by
  have hτinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    ext n
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
    rw [eq_intCast, map_intCast]
    constructor
    · intro h
      have : ((n : 𝓞 K) : K) = 0 := by rw [h]; rfl
      exact_mod_cast this
    · rintro rfl; simp
  have hinj : Function.Injective ((algebraMap (𝓞 K) K).comp τ) :=
    (RingOfIntegers.coe_injective (K := K)).comp hτinj
  let φ : E →+* K := IsFractionRing.lift hinj
  letI : Algebra E K := φ.toAlgebra
  have hmap : τ = algebraMap (𝓞 E) (𝓞 K) := by
    ext x
    change ((algebraMap (𝓞 K) K).comp τ) x = φ (algebraMap (𝓞 E) E x)
    rw [IsFractionRing.lift_algebraMap]
  have htower := Module.finrank_mul_finrank ℚ E K
  have hE : 0 < Module.finrank ℚ E := Module.finrank_pos
  refine ⟨⟨Module.finrank E K, htower.symm⟩, ?_⟩
  have hq : Module.finrank ℚ K / Module.finrank ℚ E = Module.finrank E K := by
    rw [← htower, Nat.mul_div_cancel_left _ hE]
  rw [hq, hmap, Ideal.absNorm_algebraMap (𝓞 E) (𝓞 K) 𝔞,
    ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 K) K]

end GlobalTheory
