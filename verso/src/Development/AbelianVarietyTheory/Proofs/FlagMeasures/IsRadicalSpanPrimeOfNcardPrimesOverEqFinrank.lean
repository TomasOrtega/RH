import Mathlib

open NumberField UniqueFactorizationMonoid

namespace GlobalTheory.SplitRadical

/- English proof (translation)
Introduce `x hx`. Take `⟨n, hn⟩` from `hx`. Establish `h1 : I ∣ Ideal.span {x} ^ n`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]`. Conclude with `hn`.

Establish `h2 : I ∣ Ideal.span {x}` using `hI.isRadical n _ h1`. Conclude with `(Ideal.span_singleton_le_iff_mem I).1 (Ideal.dvd_iff_le.1 h2)`.
-/
theorem isRadical_of_squarefree {S : Type} [CommRing S] [IsDedekindDomain S] {I : Ideal S}
    (hI : Squarefree I) : I.IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have h1 : I ∣ Ideal.span {x} ^ n := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact hn
  have h2 : I ∣ Ideal.span {x} := hI.isRadical n _ h1
  exact (Ideal.span_singleton_le_iff_mem I).1 (Ideal.dvd_iff_le.1 h2)

/- English proof (translation)
Introduce `E _ _ p hp hcard`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hP`. Establish `hPmax : P.IsMaximal` using `Int.ideal_span_isMaximal_of_prime p`. Establish `hP0 : P ≠ ⊥`.

Rewrite using `[hP, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hp.ne_zero` after adjusting the coercions. Establish `hmap : Ideal.span {(p : 𝓞 E)} = P.map (algebraMap ℤ (𝓞 E))`. Rewrite using `[hP, Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `hmap0 : P.map (algebraMap ℤ (𝓞 E)) ≠ ⊥` using `Ideal.map_ne_bot_of_ne_bot hP0`.

Establish `hsum` using `Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)`. Rewrite `hsum` using `[NumberField.RingOfIntegers.rank, ← hcard, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.card_eq_sum_ones]`. Establish `hge : ∀ q ∈ (Finset.univ : Finset (P.primesOver (𝓞 E))), 1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ`. Introduce `q _`. Use `haveI : q.1.IsPrime := q.2.1`.

Conclude with `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')`. Establish `hone : ∀ q : P.primesOver (𝓞 E), q.1.ramificationIdx ℤ = 1`. Introduce `q`. Use `(Finset.sum_eq_sum_iff_of_le hge).1 hsum.symm q (Finset.mem_univ q)` as an intermediate fact. Conclude with `Nat.eq_one_of_mul_eq_one_right this.symm`.

Rewrite using `[hmap]`. Apply `isRadical_of_squarefree` to reduce the goal to its premises. Rewrite using `[UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hmap0, Multiset.nodup_iff_count_le_one]`. Introduce `q`. Distinguish the cases in `hq : q ∈ UniqueFactorizationMonoid.normalizedFactors (P.map (algebraMap ℤ (𝓞 E)))`.

Establish `hqprime : q.IsPrime` using `Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor q hq)`. Establish `hle : P.map (algebraMap ℤ (𝓞 E)) ≤ q` using `Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq)`. Establish `hlo : q.LiesOver P` using `⟨hPmax.eq_of_le (Ideal.comap_ne_top _ hqprime.ne_top) (Ideal.map_le_iff_le_comap.1 hle)⟩`. Rewrite using `[← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count P q hmap0]`. Conclude with `(hone ⟨q, hqprime, hlo⟩).le`.

Rewrite using `[Multiset.count_eq_zero.2 hq]`. Conclude with `zero_le_one`.
-/
theorem isRadical_span_of_ncard_primesOver : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime →
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E →
    (Ideal.span {(p : 𝓞 E)}).IsRadical := by
  intro E _ _ p hp hcard
  haveI : Fact p.Prime := ⟨hp⟩
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hP
  have hPmax : P.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hP0 : P ≠ ⊥ := by
    rw [hP, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hmap : Ideal.span {(p : 𝓞 E)} = P.map (algebraMap ℤ (𝓞 E)) := by
    rw [hP, Ideal.map_span, Set.image_singleton, map_natCast]
  have hmap0 : P.map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hP0

  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
  rw [NumberField.RingOfIntegers.rank, ← hcard, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    ← Finset.card_univ, Finset.card_eq_sum_ones] at hsum

  have hge : ∀ q ∈ (Finset.univ : Finset (P.primesOver (𝓞 E))),
      1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q _
    haveI : q.1.IsPrime := q.2.1
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne'
      (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  have hone : ∀ q : P.primesOver (𝓞 E), q.1.ramificationIdx ℤ = 1 := by
    intro q
    have := (Finset.sum_eq_sum_iff_of_le hge).1 hsum.symm q (Finset.mem_univ q)
    exact Nat.eq_one_of_mul_eq_one_right this.symm

  rw [hmap]
  apply isRadical_of_squarefree
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hmap0,
    Multiset.nodup_iff_count_le_one]
  intro q
  by_cases hq : q ∈ UniqueFactorizationMonoid.normalizedFactors (P.map (algebraMap ℤ (𝓞 E)))
  · have hqprime : q.IsPrime :=
      Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor q hq)
    have hle : P.map (algebraMap ℤ (𝓞 E)) ≤ q :=
      Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq)
    have hlo : q.LiesOver P :=
      ⟨hPmax.eq_of_le (Ideal.comap_ne_top _ hqprime.ne_top) (Ideal.map_le_iff_le_comap.1 hle)⟩
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count P q hmap0]
    exact (hone ⟨q, hqprime, hlo⟩).le
  · rw [Multiset.count_eq_zero.2 hq]
    exact zero_le_one

end GlobalTheory.SplitRadical
