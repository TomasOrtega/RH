import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Establish `hspan : Ideal.span {d} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hd`. Establish `hirr : Irreducible P.asIdeal` using `(Ideal.prime_of_isPrime P.ne_bot P.isPrime).irreducible`. Take `⟨a, J, hPJ, hdJ⟩` from `WfDvdMonoid.max_power_factor hspan hirr`.

Establish `hJP : ¬ J ≤ P.asIdeal` using `fun h => hPJ (Ideal.dvd_iff_le.mpr h)`. Take `⟨s, hsJ, hsP⟩` from `Set.not_subset.mp hJP`. Establish `hsJ' : J ∣ Ideal.span {s}` using `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hsJ)`. Establish `hvPs : P.valuation K (s : K) = 1`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`.

Use `le_antisymm (P.intValuation_le_one s) (not_lt.mp fun h => hsP ?_)` and prove the remaining obligations. Rewrite `h` using `[HeightOneSpectrum.intValuation_lt_one_iff_dvd, Ideal.dvd_span_singleton]`. Conclude with `h`. Establish `hQ : ∀ Q : HeightOneSpectrum (𝓞 K), Q ≠ P → Q.intValuation s ≤ Q.intValuation d`. Introduce `Q hQP`.

Establish `hQd : Q.intValuation d = WithZero.exp (-((Associates.mk Q.asIdeal).count (Associates.mk (Ideal.span {d})).factors : ℤ))`. Rewrite using `[HeightOneSpectrum.intValuation_def, if_neg hd]`. Use `set n := (Associates.mk Q.asIdeal).count (Associates.mk (Ideal.span {d})).factors`. Establish `hdiv : Q.asIdeal ^ n ∣ Ideal.span {d}` using `(Q.intValuation_le_pow_iff_dvd d n).mp (le_of_eq hQd)`. Establish `hne : Q.asIdeal ≠ P.asIdeal` using `fun h => hQP (HeightOneSpectrum.ext h)`.

Establish `hcop : IsCoprime Q.asIdeal P.asIdeal` using `Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne Q.isMaximal P.isMaximal hne)`. Establish `hcopn : IsCoprime (Q.asIdeal ^ n) (P.asIdeal ^ a)` using `hcop.pow`. Rewrite `hdiv` using `[hdJ]`. Establish `hQJ : Q.asIdeal ^ n ∣ J` using `hcopn.dvd_of_dvd_mul_left hdiv`. Rewrite using `[hQd]`.

Conclude with `(Q.intValuation_le_pow_iff_dvd s n).mpr (hQJ.trans hsJ')`. Use `⟨s, hvPs, fun t ht => ?_⟩` and prove the remaining obligations. Establish `hdt : (d : K) * t ∈ (algebraMap (𝓞 K) K).range` using `⟨⟨_, hdT t ht⟩, rfl⟩`. Take `⟨y, hy⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one K ((s : K) * t) (by`. Introduce `Q`.

Distinguish the cases in `hQP : Q = P`. Substitute `hQP` using the available equality. Rewrite using `[map_mul, hvPs, one_mul]`. Conclude with `hPT t ht`. Take `⟨z, hz⟩` from `hdt`.

Establish `h1 : Q.valuation K ((d : K) * t) ≤ 1`. Rewrite using `[← hz]`. Conclude with `Q.valuation_le_one z`. Rewrite `h1`, the goal using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `hQ Q hQP`. Use `_ ≤ 1 := h1)`. Rewrite using `[← hy]`. Conclude with `RingOfIntegers.isIntegral_coe y`.
-/
theorem exists_unit_at_prime_mul_integral (K : Type) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) (T : Set K) (d : 𝓞 K) (hd : d ≠ 0)
    (hdT : ∀ t ∈ T, IsIntegral ℤ ((d : K) * t)) (hPT : ∀ t ∈ T, P.valuation K t ≤ 1) :
    ∃ s : 𝓞 K, P.valuation K (s : K) = 1 ∧ ∀ t ∈ T, IsIntegral ℤ ((s : K) * t) := by
  have hspan : Ideal.span {d} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd
  have hirr : Irreducible P.asIdeal := (Ideal.prime_of_isPrime P.ne_bot P.isPrime).irreducible
  obtain ⟨a, J, hPJ, hdJ⟩ := WfDvdMonoid.max_power_factor hspan hirr
  have hJP : ¬ J ≤ P.asIdeal := fun h => hPJ (Ideal.dvd_iff_le.mpr h)
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.mp hJP
  have hsJ' : J ∣ Ideal.span {s} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hsJ)
  have hvPs : P.valuation K (s : K) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    refine le_antisymm (P.intValuation_le_one s) (not_lt.mp fun h => hsP ?_)
    rw [HeightOneSpectrum.intValuation_lt_one_iff_dvd, Ideal.dvd_span_singleton] at h
    exact h

  have hQ : ∀ Q : HeightOneSpectrum (𝓞 K), Q ≠ P → Q.intValuation s ≤ Q.intValuation d := by
    intro Q hQP
    have hQd : Q.intValuation d = WithZero.exp (-((Associates.mk Q.asIdeal).count
        (Associates.mk (Ideal.span {d})).factors : ℤ)) := by
      rw [HeightOneSpectrum.intValuation_def, if_neg hd]
    set n := (Associates.mk Q.asIdeal).count (Associates.mk (Ideal.span {d})).factors
    have hdiv : Q.asIdeal ^ n ∣ Ideal.span {d} :=
      (Q.intValuation_le_pow_iff_dvd d n).mp (le_of_eq hQd)
    have hne : Q.asIdeal ≠ P.asIdeal := fun h => hQP (HeightOneSpectrum.ext h)
    have hcop : IsCoprime Q.asIdeal P.asIdeal :=
      Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne Q.isMaximal P.isMaximal hne)
    have hcopn : IsCoprime (Q.asIdeal ^ n) (P.asIdeal ^ a) := hcop.pow
    rw [hdJ] at hdiv
    have hQJ : Q.asIdeal ^ n ∣ J := hcopn.dvd_of_dvd_mul_left hdiv
    rw [hQd]
    exact (Q.intValuation_le_pow_iff_dvd s n).mpr (hQJ.trans hsJ')
  refine ⟨s, hvPs, fun t ht => ?_⟩
  have hdt : (d : K) * t ∈ (algebraMap (𝓞 K) K).range := ⟨⟨_, hdT t ht⟩, rfl⟩
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((s : K) * t) (by
    intro Q
    by_cases hQP : Q = P
    · subst hQP
      rw [map_mul, hvPs, one_mul]; exact hPT t ht
    · obtain ⟨z, hz⟩ := hdt
      have h1 : Q.valuation K ((d : K) * t) ≤ 1 := by
        rw [← hz]; exact Q.valuation_le_one z
      rw [map_mul] at h1 ⊢
      calc Q.valuation K (s : K) * Q.valuation K t ≤ Q.valuation K (d : K) * Q.valuation K t := by
            gcongr
            rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
            exact hQ Q hQP
        _ ≤ 1 := h1)
  rw [← hy]
  exact RingOfIntegers.isIntegral_coe y

end GlobalTheory
