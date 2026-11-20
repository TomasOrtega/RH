import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Simplify using `[ha]`. Establish `h1 : P.intValuation a = WithZero.exp (-((Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal R)).factors : ℕ) : ℤ)` using `P.intValuation_if_neg ha`. Use `set k := (Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal R)).factors`. Establish `h2 : a ∈ P.asIdeal ^ k` using `(P.intValuation_le_pow_iff_mem a k).1 h1.le`.

Rewrite using `[h1, P.intValuation_le_pow_iff_mem]`. Establish `h3 : (P.asIdeal ^ k).map σ ≤ P.asIdeal ^ k`. Rewrite using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono h k`. Conclude with `h3 (Ideal.mem_map_of_mem σ h2)`.
-/
theorem intValuation_map_le_of_map_le {R : Type} [CommRing R] [IsDedekindDomain R] (σ : R →+* R)
    (P : HeightOneSpectrum R) (h : P.asIdeal.map σ ≤ P.asIdeal) (a : R) :
    P.intValuation (σ a) ≤ P.intValuation a := by
  by_cases ha : a = 0
  · simp [ha]
  have h1 : P.intValuation a = WithZero.exp (-((Associates.mk P.asIdeal).count
      (Associates.mk (Ideal.span {a} : Ideal R)).factors : ℕ) : ℤ) := P.intValuation_if_neg ha
  set k := (Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal R)).factors
  have h2 : a ∈ P.asIdeal ^ k := (P.intValuation_le_pow_iff_mem a k).1 h1.le
  rw [h1, P.intValuation_le_pow_iff_mem]
  have h3 : (P.asIdeal ^ k).map σ ≤ P.asIdeal ^ k := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h k
  exact h3 (Ideal.mem_map_of_mem σ h2)

/- English proof (translation)
Introduce `F E _ _ _ _ _ c hc u P hu hP`. Set `σ : 𝓞 E →+* 𝓞 E` to `RingOfIntegers.mapRingHom (c : E →+* E)`. Establish `hσ : ∀ a : 𝓞 E, ((σ a : 𝓞 E) : E) = c (a : E)` using `fun a => rfl`. Establish `hσσ : ∀ a, σ (σ a) = a` using `fun a => by`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Rewrite using `[hσ, hσ, hc]`. Establish `hle : P.asIdeal.map σ ≤ P.asIdeal`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Assume the negation of the conclusion as `hb`.

Conclude with `hP ⟨a, ha, σ a, hσ a, hb⟩`. Establish `hint : ∀ a, P.intValuation (σ a) = P.intValuation a` using `fun a => by`. Apply `le_antisymm (intValuation_map_le_of_map_le σ P hle a)` to reduce the goal to its premises. Use `intValuation_map_le_of_map_le σ P hle (σ a)` as an intermediate fact. Rewrite `this` using `[hσσ]`. Then use the resulting hypothesis.

Establish `hval : ∀ a : 𝓞 E, P.valuation E (c (a : E)) = P.valuation E (a : E)` using `fun a => by`. Rewrite using `[← hσ]`. Express the relevant statement in the definitionally equal form `P.valuation E (algebraMap (𝓞 E) E (σ a)) = P.valuation E (algebraMap (𝓞 E) E a)`. Rewrite using `[P.valuation_of_algebraMap, P.valuation_of_algebraMap, hint]`. Establish `hcu : P.valuation E (c u) = P.valuation E u`.

Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) u`. Rewrite using `[map_div₀, map_div₀, map_div₀]`. Conclude with `congrArg₂ (· / ·) (hval a) (hval b)`. Establish `h2 : P.valuation E u ^ 2 = 1`. Use `congrArg (P.valuation E) hu` as an intermediate fact.

Rewrite `this` using `[map_mul, hcu, map_one, ← sq]`. Then use the resulting hypothesis. Conclude with `(pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h2`.
-/
theorem valuation_eq_one_of_norm_one_of_not_moved :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E),
      (∀ x, c (c x) = x) → ∀ (u : E) (P : HeightOneSpectrum (𝓞 E)), u * c u = 1 →
        ¬ Moved c P.asIdeal → P.valuation E u = 1 := by
  intro F E _ _ _ _ _ c hc u P hu hP
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (c : E →+* E)
  have hσ : ∀ a : 𝓞 E, ((σ a : 𝓞 E) : E) = c (a : E) := fun a => rfl
  have hσσ : ∀ a, σ (σ a) = a := fun a => by
    apply RingOfIntegers.ext
    rw [hσ, hσ, hc]
  have hle : P.asIdeal.map σ ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    by_contra hb
    exact hP ⟨a, ha, σ a, hσ a, hb⟩
  have hint : ∀ a, P.intValuation (σ a) = P.intValuation a := fun a => by
    apply le_antisymm (intValuation_map_le_of_map_le σ P hle a)
    have := intValuation_map_le_of_map_le σ P hle (σ a)
    rwa [hσσ] at this
  have hval : ∀ a : 𝓞 E, P.valuation E (c (a : E)) = P.valuation E (a : E) := fun a => by
    rw [← hσ]
    change P.valuation E (algebraMap (𝓞 E) E (σ a)) = P.valuation E (algebraMap (𝓞 E) E a)
    rw [P.valuation_of_algebraMap, P.valuation_of_algebraMap, hint]
  have hcu : P.valuation E (c u) = P.valuation E u := by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) u
    rw [map_div₀, map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hval a) (hval b)
  have h2 : P.valuation E u ^ 2 = 1 := by
    have := congrArg (P.valuation E) hu
    rwa [map_mul, hcu, map_one, ← sq] at this
  exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h2

end GlobalTheory.UnRep
