import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermT

open NumberField IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

/- English proof (translation)
Introduce `F _ _ t z c u hu hz`. Distinguish the cases in `hc : (c : F) = 0`. Use `⟨1, t.asIdeal.primeCompl.one_mem, 0, ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[hc, map_zero, zero_mul]`. Establish `hz0 : z = 0` using `(algebraMap F (t.adicCompletion F)).injective (by rw [hz, map_zero])`.

Simplify using `[hz0]`. Establish `hxu : algebraMap F (t.adicCompletion F) (z / (c : F)) = u`. Rewrite using `[map_div₀, hz, mul_div_cancel_left₀ _ ((map_ne_zero _).2 hc)]`. Establish `hu' : algebraMap F (t.adicCompletion F) (z / (c : F)) ∈ t.adicCompletionIntegers F` using `hxu ▸ hu`. Establish `e : ∀ x : F, Valued.v (algebraMap F (t.adicCompletion F) x) = t.valuation F x`.

Introduce `x`. Use `first`. Consider the case `exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' t x`. Consider the case `exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' x`. Consider the case `exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation t x`.

Consider the case `exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation x`. Consider the case `simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Consider the case `rfl`. Establish `hv : t.valuation F (z / (c : F)) ≤ 1`. Rewrite `hu'` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`.

Rewrite using `[← e]`. Conclude with `hu'`. Take `⟨n, m, hm, hnm⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) (z / (c : F))`. Establish `hm0 : m ≠ 0` using `nonZeroDivisors.ne_zero hm`. Establish `hvm : t.intValuation m ≠ 0` using `HeightOneSpectrum.intValuation_ne_zero t m hm0`.

Establish `hnm' : t.intValuation n ≤ t.intValuation m`. Rewrite `hv` using `[← hnm, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(div_le_one₀ (zero_lt_iff.2 hvm)).1 hv`. Establish `hI0 : Ideal.span {m} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `hm0`. Take `⟨k, J, hJt, hmJ⟩` from `WfDvdMonoid.max_power_factor hI0 t.irreducible`. Establish `hnk : n ∈ t.asIdeal ^ k`. Establish `hdm : t.asIdeal ^ k ∣ Ideal.span {m}` using `⟨J, hmJ⟩`. Rewrite `hdm` using `[← HeightOneSpectrum.intValuation_le_pow_iff_dvd]`.

Establish `hdn` using `(HeightOneSpectrum.intValuation_le_pow_iff_dvd t n k).1 (hnm'.trans hdm)`. Conclude with `Ideal.dvd_span_singleton.1 hdn`. Establish `hJ : ¬ J ≤ t.asIdeal` using `fun h => hJt (Ideal.dvd_iff_le.2 h)`. Take `⟨d, hdJ, hdt⟩` from `SetLike.not_le_iff_exists.1 hJ`. Establish `hdn : d * n ∈ Ideal.span {m}`.

Rewrite using `[hmJ, mul_comm d n]`. Conclude with `Ideal.mul_mem_mul hnk hdJ`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 hdn`. Use `⟨d, hdt, a, ?_⟩` and prove the remaining obligations. Establish `hmF : algebraMap (𝓞 F) F m ≠ 0`.

Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]` and apply the resulting hypothesis. Establish `ha' : algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F m = algebraMap (𝓞 F) F d * algebraMap (𝓞 F) F n`. Rewrite using `[← map_mul, ← map_mul, ha]`. Establish `hzm : z * algebraMap (𝓞 F) F m = (c : F) * algebraMap (𝓞 F) F n`. Establish `h3 : z = (c : F) * (algebraMap (𝓞 F) F n / algebraMap (𝓞 F) F m)`.

Rewrite using `[hnm]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h3, mul_assoc, div_mul_cancel₀ _ hmF]`. Use `show z * algebraMap (𝓞 F) F d = (c : F) * algebraMap (𝓞 F) F a`. Apply `mul_right_cancel₀ hmF` to reduce the goal to its premises.

Take the linear combination `(algebraMap (𝓞 F) F d) * hzm - (c : F) * ha'`.
-/
theorem local_integral_of_substitution : LocInt := by
  intro F _ _ t z c u hu hz
  by_cases hc : (c : F) = 0
  · refine ⟨1, t.asIdeal.primeCompl.one_mem, 0, ?_⟩
    rw [hc, map_zero, zero_mul] at hz
    have hz0 : z = 0 := (algebraMap F (t.adicCompletion F)).injective (by rw [hz, map_zero])
    simp [hz0]
  · have hxu : algebraMap F (t.adicCompletion F) (z / (c : F)) = u := by
      rw [map_div₀, hz, mul_div_cancel_left₀ _ ((map_ne_zero _).2 hc)]
    have hu' : algebraMap F (t.adicCompletion F) (z / (c : F)) ∈ t.adicCompletionIntegers F :=
      hxu ▸ hu
    have e : ∀ x : F, Valued.v (algebraMap F (t.adicCompletion F) x) = t.valuation F x := by
      intro x
      first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' t x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation t x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation x
      | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      | rfl
    have hv : t.valuation F (z / (c : F)) ≤ 1 := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hu'
      rw [← e]
      exact hu'
    obtain ⟨n, m, hm, hnm⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (z / (c : F))
    have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
    have hvm : t.intValuation m ≠ 0 := HeightOneSpectrum.intValuation_ne_zero t m hm0
    have hnm' : t.intValuation n ≤ t.intValuation m := by
      rw [← hnm, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.valuation_of_algebraMap] at hv
      exact (div_le_one₀ (zero_lt_iff.2 hvm)).1 hv
    have hI0 : Ideal.span {m} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hm0
    obtain ⟨k, J, hJt, hmJ⟩ := WfDvdMonoid.max_power_factor hI0 t.irreducible
    have hnk : n ∈ t.asIdeal ^ k := by
      have hdm : t.asIdeal ^ k ∣ Ideal.span {m} := ⟨J, hmJ⟩
      rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd] at hdm
      have hdn := (HeightOneSpectrum.intValuation_le_pow_iff_dvd t n k).1 (hnm'.trans hdm)
      exact Ideal.dvd_span_singleton.1 hdn
    have hJ : ¬ J ≤ t.asIdeal := fun h => hJt (Ideal.dvd_iff_le.2 h)
    obtain ⟨d, hdJ, hdt⟩ := SetLike.not_le_iff_exists.1 hJ
    have hdn : d * n ∈ Ideal.span {m} := by
      rw [hmJ, mul_comm d n]
      exact Ideal.mul_mem_mul hnk hdJ
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hdn
    refine ⟨d, hdt, a, ?_⟩
    have hmF : algebraMap (𝓞 F) F m ≠ 0 := by
      rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
    have ha' : algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F m =
        algebraMap (𝓞 F) F d * algebraMap (𝓞 F) F n := by
      rw [← map_mul, ← map_mul, ha]
    have hzm : z * algebraMap (𝓞 F) F m = (c : F) * algebraMap (𝓞 F) F n := by
      have h3 : z = (c : F) * (algebraMap (𝓞 F) F n / algebraMap (𝓞 F) F m) := by
        rw [hnm]
        field_simp
      rw [h3, mul_assoc, div_mul_cancel₀ _ hmF]
    show z * algebraMap (𝓞 F) F d = (c : F) * algebraMap (𝓞 F) F a
    apply mul_right_cancel₀ hmF
    linear_combination (algebraMap (𝓞 F) F d) * hzm - (c : F) * ha'

end PI.UnitaryGroupMassFormula.UJClassMass

end
