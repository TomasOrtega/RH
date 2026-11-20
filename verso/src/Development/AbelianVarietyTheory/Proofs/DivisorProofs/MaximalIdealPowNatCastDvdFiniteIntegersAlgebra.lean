import Mathlib

namespace GlobalTheory

open IsLocalRing

/- English proof (translation)
Introduce `p hp C _ _ v O _ _ hv A _ _ _ _ a ha`. Use `set J : Ideal O := (maximalIdeal A).comap (algebraMap O A) with hJdef`. Use `haveI : J.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal A)`. Establish `hJp : ∀ c ∈ J, ∃ k : ℕ, (p : O) ∣ c ^ k`. Introduce `c hc`.

Establish `hlt : v (algebraMap O C c) < 1`. Use `lt_of_le_of_ne (hv.map_le_one c) ?_` and prove the remaining obligations. Introduce `h1`. Establish `hu : IsUnit c` using `hv.isUnit_of_one' h1`. Establish `: IsUnit (algebraMap O A c)` using `hu.map _`.

Conclude with `(maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ hc this)`. Establish `hp0 : 0 < v (algebraMap O C (p : O))`. Rewrite using `[map_natCast]`. Conclude with `(Valuation.pos_iff v).2 (Nat.cast_ne_zero.2 hp)`. Take `⟨k, hk⟩` from `NNReal.exists_pow_lt_of_lt_one hp0 hlt`.

Use `⟨k, hv.dvd_of_le ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, map_pow]`. Conclude with `hk.le`. Establish `hI : J.map (algebraMap O A) ≤ (Ideal.span {(p : A)}).radical`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `c hc`. Take `⟨k, d, hd⟩` from `hJp c hc`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_span_singleton]`. Use `⟨algebraMap O A d, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_pow, hd, map_mul, map_natCast]`. Establish `ha' : a ∈ (J.map (algebraMap O A)).radical`. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`. Introduce and unpack `Q ⟨hQ, hQp⟩`. Establish `hle : J ≤ Q.comap (algebraMap O A)` using `Ideal.map_le_iff_le_comap.1 hQ`.

Establish `hQc : Q.comap (algebraMap O A) = J` using `((inferInstance : J.IsMaximal).eq_of_le (Ideal.IsPrime.comap (algebraMap O A)).ne_top hle).symm`. Use `haveI : (Q.comap (algebraMap O A)).IsMaximal := by rw [hQc]; infer_instance`. Use `haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q this`. Rewrite using `[IsLocalRing.eq_maximalIdeal this]`. Conclude with `ha`.

Establish `h2 : a ∈ (Ideal.span {(p : A)}).radical`. Use `Ideal.radical_mono hI ha'` as an intermediate fact. Rewrite `this` using `[Ideal.radical_idem]`. Then use the resulting hypothesis. Take `⟨N, hN⟩` from `h2`. Conclude with `⟨N, Ideal.mem_span_singleton.1 hN⟩`.
-/
theorem maxIdeal_pow_dvd_natCast_of_integers :
    ∀ (p : ℕ), p ≠ 0 → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type)
      [CommRing O] [Algebra O C], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A]
      [Module.Finite O A] [IsLocalRing A] (a : A), a ∈ IsLocalRing.maximalIdeal A →
      ∃ N : ℕ, (p : A) ∣ a ^ N := by
  intro p hp C _ _ v O _ _ hv A _ _ _ _ a ha

  set J : Ideal O := (maximalIdeal A).comap (algebraMap O A) with hJdef
  haveI : J.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal A)

  have hJp : ∀ c ∈ J, ∃ k : ℕ, (p : O) ∣ c ^ k := by
    intro c hc
    have hlt : v (algebraMap O C c) < 1 := by
      refine lt_of_le_of_ne (hv.map_le_one c) ?_
      intro h1
      have hu : IsUnit c := hv.isUnit_of_one' h1
      have : IsUnit (algebraMap O A c) := hu.map _
      exact (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ hc this)
    have hp0 : 0 < v (algebraMap O C (p : O)) := by
      rw [map_natCast]
      exact (Valuation.pos_iff v).2 (Nat.cast_ne_zero.2 hp)
    obtain ⟨k, hk⟩ := NNReal.exists_pow_lt_of_lt_one hp0 hlt
    refine ⟨k, hv.dvd_of_le ?_⟩
    rw [map_pow, map_pow]
    exact hk.le

  have hI : J.map (algebraMap O A) ≤ (Ideal.span {(p : A)}).radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    obtain ⟨k, d, hd⟩ := hJp c hc
    refine ⟨k, ?_⟩
    rw [Ideal.mem_span_singleton]
    refine ⟨algebraMap O A d, ?_⟩
    rw [← map_pow, hd, map_mul, map_natCast]

  have ha' : a ∈ (J.map (algebraMap O A)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hQ, hQp⟩
    have hle : J ≤ Q.comap (algebraMap O A) := Ideal.map_le_iff_le_comap.1 hQ
    have hQc : Q.comap (algebraMap O A) = J :=
      ((inferInstance : J.IsMaximal).eq_of_le (Ideal.IsPrime.comap (algebraMap O A)).ne_top hle).symm
    haveI : (Q.comap (algebraMap O A)).IsMaximal := by rw [hQc]; infer_instance
    haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q this
    rw [IsLocalRing.eq_maximalIdeal this]
    exact ha
  have h2 : a ∈ (Ideal.span {(p : A)}).radical := by
    have := Ideal.radical_mono hI ha'
    rwa [Ideal.radical_idem] at this
  obtain ⟨N, hN⟩ := h2
  exact ⟨N, Ideal.mem_span_singleton.1 hN⟩

end GlobalTheory
