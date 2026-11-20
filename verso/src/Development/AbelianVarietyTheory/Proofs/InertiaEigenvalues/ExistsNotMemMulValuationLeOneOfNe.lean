import Mathlib
open IsDedekindDomain NumberField

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ p ι _ x`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F)) x`. Establish `hc : (b : 𝓞 F) ≠ 0` using `nonZeroDivisors.ne_zero b.2`. Establish `hfin : FiniteMultiplicity p.asIdeal (Ideal.span {(b : 𝓞 F)})` using `FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact p.isPrime.ne_top) (by simpa using hc)`. Take `⟨J, hJ, hnd⟩` from `hfin.exists_eq_pow_mul_and_not_dvd`.

Establish `hJp : ¬ J ≤ p.asIdeal` using `fun h => hnd (Ideal.dvd_iff_le.mpr h)`. Take `⟨s, hsJ, hsp⟩` from `SetLike.not_le_iff_exists.mp hJp`. Use `⟨s, hsp, fun q hq i => ?_⟩` and prove the remaining obligations. Establish `hpow : ¬ p.asIdeal ^ multiplicity p.asIdeal (Ideal.span {(b : 𝓞 F)}) ≤ q.asIdeal`. Introduce `h`.

Establish `h1 : p.asIdeal ≤ q.asIdeal` using `q.isPrime.le_of_pow_le h`. Conclude with `hq (HeightOneSpectrum.ext (p.isMaximal.eq_of_le q.isPrime.ne_top h1).symm)`. Take `⟨t, ht, htq⟩` from `SetLike.not_le_iff_exists.mp hpow`. Establish `hts : t * s ∈ Ideal.span {(b : 𝓞 F)}`. Rewrite using `[hJ]`.

Conclude with `Ideal.mul_mem_mul ht hsJ`. Take `⟨u, hu⟩` from `Ideal.mem_span_singleton.mp hts`. Take `⟨a, ha⟩` from `hb i`. Use `replace ha : algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F (b : 𝓞 F) * x i := by`. Rewrite using `[ha]`.

Conclude with `Algebra.smul_def _ _`. Establish `key : algebraMap (𝓞 F) F t * ((s : F) * x i) = algebraMap (𝓞 F) F (u * a)`. Rewrite using `[map_mul, ha, RingOfIntegers.coe_eq_algebraMap, ← mul_assoc, ← map_mul, hu, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : q.valuation F (algebraMap (𝓞 F) F t) = 1` using `(q.valuation_eq_one_iff_notMem (K := F) (r := t)).2 htq`.

Establish `h2 : q.valuation F (algebraMap (𝓞 F) F (u * a)) ≤ 1` using `q.valuation_le_one (K := F) _`. Rewrite `h2` using `[← key, map_mul, h1, one_mul]`. Conclude with `h2`.
-/
theorem exists_notMem_mul_valuation_le_one_of_ne : ∀ {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (𝓞 F)) {ι : Type} [Finite ι] (x : ι → F), ∃ s : 𝓞 F, s ∉ p.asIdeal ∧
      ∀ q : HeightOneSpectrum (𝓞 F), q ≠ p → ∀ i, q.valuation F ((s : F) * x i) ≤ 1 := by
  intro F _ _ p ι _ x
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F)) x
  have hc : (b : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hfin : FiniteMultiplicity p.asIdeal (Ideal.span {(b : 𝓞 F)}) :=
    FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact p.isPrime.ne_top)
      (by simpa using hc)
  obtain ⟨J, hJ, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hJp : ¬ J ≤ p.asIdeal := fun h => hnd (Ideal.dvd_iff_le.mpr h)
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.mp hJp
  refine ⟨s, hsp, fun q hq i => ?_⟩
  have hpow : ¬ p.asIdeal ^ multiplicity p.asIdeal (Ideal.span {(b : 𝓞 F)}) ≤ q.asIdeal := by
    intro h
    have h1 : p.asIdeal ≤ q.asIdeal := q.isPrime.le_of_pow_le h
    exact hq (HeightOneSpectrum.ext (p.isMaximal.eq_of_le q.isPrime.ne_top h1).symm)
  obtain ⟨t, ht, htq⟩ := SetLike.not_le_iff_exists.mp hpow
  have hts : t * s ∈ Ideal.span {(b : 𝓞 F)} := by
    rw [hJ]; exact Ideal.mul_mem_mul ht hsJ
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hts
  obtain ⟨a, ha⟩ := hb i
  replace ha : algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F (b : 𝓞 F) * x i := by
    rw [ha]; exact Algebra.smul_def _ _
  have key : algebraMap (𝓞 F) F t * ((s : F) * x i) = algebraMap (𝓞 F) F (u * a) := by
    rw [map_mul, ha, RingOfIntegers.coe_eq_algebraMap, ← mul_assoc, ← map_mul, hu, map_mul]
    ring
  have h1 : q.valuation F (algebraMap (𝓞 F) F t) = 1 :=
    (q.valuation_eq_one_iff_notMem (K := F) (r := t)).2 htq
  have h2 : q.valuation F (algebraMap (𝓞 F) F (u * a)) ≤ 1 := q.valuation_le_one (K := F) _
  rw [← key, map_mul, h1, one_mul] at h2
  exact h2

end GlobalTheory
