import Mathlib

open NumberField

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ p hp h`. Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Establish `hp0 : Ideal.span {(p : ℤ)} ≠ ⊥`. Simplify `hp.ne_zero` using `[Ideal.span_singleton_eq_bot]`. Use `haveI hpr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ`.

Use `haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hpr.isMaximal hp0`. Establish `hsum` using `Ideal.sum_ramification_inertia (𝓞 E) ℚ E (p := Ideal.span {(p : ℤ)}) hp0`. Rewrite using `[← hsum, ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset, Finset.card_eq_sum_ones]`. Use `Finset.sum_congr rfl fun P hP => ?_` and prove the remaining obligations. Rewrite `hP` using `[IsDedekindDomain.mem_primesOverFinset_iff hp0]`.

Take `⟨hPp, hPl⟩` from `hP`. Establish `hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)}`. Simplify using `[Ideal.map_span]`. Establish `hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Conclude with `hPl.over.le`. Establish `hmem : (p : 𝓞 E) ∈ P`. Rewrite `hle` using `[hmap, Ideal.span_singleton_le_iff_mem]`. Conclude with `hle`. Establish `hPm : P.IsMaximal` using `Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})`.

Take `⟨hN, hsq⟩` from `h P hPm hmem`. Establish `he : (Ideal.span {(p : ℤ)}).ramificationIdx' P = 1`. Assume the negation of the conclusion as `hne`. Use `(Ideal.ramificationIdx'_ne_one_iff hle).mp hne` as an intermediate fact. Rewrite `this` using `[hmap, Ideal.span_singleton_le_iff_mem]`.

Conclude with `hsq this`. Establish `hf : (Ideal.span {(p : ℤ)}).inertiaDeg' P = 1`. Establish `h1` using `Ideal.absNorm_eq_pow_inertiaDeg' P hp`. Rewrite `h1` using `[hN]`. Conclude with `(Nat.pow_right_injective hp.two_le (by simpa using h1)).symm`.

Rewrite using `[he, hf]`.
-/
theorem ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime →
      (∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) →
        Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) →
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  intro E _ _ p hp h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  haveI hpr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hpr.isMaximal hp0
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) ℚ E (p := Ideal.span {(p : ℤ)}) hp0
  rw [← hsum, ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset,
    Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hp0] at hP
  obtain ⟨hPp, hPl⟩ := hP
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    simp [Ideal.map_span]
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact hPl.over.le
  have hmem : (p : 𝓞 E) ∈ P := by
    rw [hmap, Ideal.span_singleton_le_iff_mem] at hle
    exact hle
  have hPm : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})
  obtain ⟨hN, hsq⟩ := h P hPm hmem
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' P = 1 := by
    by_contra hne
    have := (Ideal.ramificationIdx'_ne_one_iff hle).mp hne
    rw [hmap, Ideal.span_singleton_le_iff_mem] at this
    exact hsq this
  have hf : (Ideal.span {(p : ℤ)}).inertiaDeg' P = 1 := by
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' P hp
    rw [hN] at h1
    exact (Nat.pow_right_injective hp.two_le (by simpa using h1)).symm
  rw [he, hf]

end GlobalTheory
