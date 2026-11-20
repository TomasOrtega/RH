import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped nonZeroDivisors

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]`. Conclude with `finprod_congr fun v => by rw [h v]`.
-/
theorem fractionalIdeal_eq_of_count_eq {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

/- English proof (translation)
Introduce `K _ _ I β h hh hβ hfg hpow`. Set `J : FractionalIdeal (𝓞 K)⁰ K` to `⟨I, FractionalIdeal.isFractional_of_fg hfg⟩`. Establish `hJI : (J : Submodule (𝓞 K) K) = I` using `rfl`. Establish `hB : FractionalIdeal.spanSingleton (𝓞 K)⁰ β ≠ 0` using `FractionalIdeal.spanSingleton_ne_zero_iff.mpr hβ`. Establish `hp : J ^ h = FractionalIdeal.spanSingleton (𝓞 K)⁰ β ^ h`.

Rewrite using `[FractionalIdeal.spanSingleton_pow]`. Apply `FractionalIdeal.coeToSubmodule_injective` to reduce the goal to its premises. Simplify using `only [FractionalIdeal.coe_pow, FractionalIdeal.coe_spanSingleton, hJI, hpow]`. Establish `hJ : J ≠ 0`. Introduce `h0`.

Rewrite `hp` using `[h0, zero_pow hh.ne']`. Conclude with `pow_ne_zero h hB hp.symm`. Establish `hJB : J = FractionalIdeal.spanSingleton (𝓞 K)⁰ β`. Use `fractionalIdeal_eq_of_count_eq hJ hB fun v => ?_` and prove the remaining obligations. Use `congrArg (FractionalIdeal.count K v) hp` as an intermediate fact.

Rewrite `this` using `[FractionalIdeal.count_pow, FractionalIdeal.count_pow]`. Conclude with `mul_left_cancel₀ (by exact_mod_cast hh.ne') this`. Rewrite using `[← hJI, hJB, FractionalIdeal.coe_spanSingleton]`.
-/
theorem submodule_eq_span_of_pow_eq_span_pow :
    ∀ (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 K) K) (β : K) (h : ℕ),
      0 < h → β ≠ 0 → I.FG → I ^ h = Submodule.span (𝓞 K) {β ^ h} →
      I = Submodule.span (𝓞 K) {β} := by
  intro K _ _ I β h hh hβ hfg hpow
  let J : FractionalIdeal (𝓞 K)⁰ K := ⟨I, FractionalIdeal.isFractional_of_fg hfg⟩
  have hJI : (J : Submodule (𝓞 K) K) = I := rfl
  have hB : FractionalIdeal.spanSingleton (𝓞 K)⁰ β ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hβ
  have hp : J ^ h = FractionalIdeal.spanSingleton (𝓞 K)⁰ β ^ h := by
    rw [FractionalIdeal.spanSingleton_pow]
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [FractionalIdeal.coe_pow, FractionalIdeal.coe_spanSingleton, hJI, hpow]
  have hJ : J ≠ 0 := by
    intro h0
    rw [h0, zero_pow hh.ne'] at hp
    exact pow_ne_zero h hB hp.symm
  have hJB : J = FractionalIdeal.spanSingleton (𝓞 K)⁰ β := by
    refine fractionalIdeal_eq_of_count_eq hJ hB fun v => ?_
    have := congrArg (FractionalIdeal.count K v) hp
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_pow] at this
    exact mul_left_cancel₀ (by exact_mod_cast hh.ne') this
  rw [← hJI, hJB, FractionalIdeal.coe_spanSingleton]

end GlobalTheory
