import Mathlib

namespace GlobalTheory.PowMulUnit

/- English proof (translation)
Establish `hK` using `Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal S) (IsLocalRing.maximalIdeal.isMaximal S).ne_top`. Establish `hex : ∃ n : ℕ, ¬ (π ^ n ∣ x)`. Assume the negation of the conclusion as `h0`. Establish `h : ∀ n : ℕ, π ^ n ∣ x` using `fun n => not_not.mp (not_exists.mp h0 n)`. Apply `hx` to reduce the goal to its premises.

Establish `hmem : x ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal S ^ n`. Use `Ideal.mem_iInf.mpr fun n => ?_` and prove the remaining obligations. Rewrite using `[hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `h n`. Rewrite `hmem` using `[hK]`.

Conclude with `hmem`. Establish `hn0 : Nat.find hex ≠ 0`. Introduce `h0`. Establish `h1` using `Nat.find_spec hex`. Rewrite `h1` using `[h0, pow_zero]`.

Conclude with `h1 (one_dvd x)`. Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero hn0`. Establish `hdk : π ^ k ∣ x`. Use `Nat.find_min hex (show k < Nat.find hex by omega)` as an intermediate fact. Conclude with `not_not.mp this`.

Take `⟨u, rfl⟩` from `hdk`. Use `⟨k, u, ?_, rfl⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hu`. Establish `hum : u ∈ IsLocalRing.maximalIdeal S` using `(IsLocalRing.mem_maximalIdeal u).mpr hu`. Rewrite `hum` using `[hπ, Ideal.mem_span_singleton]`.

Take `⟨w, rfl⟩` from `hum`. Apply `Nat.find_spec hex` to reduce the goal to its premises. Rewrite using `[hk, pow_succ]`. Conclude with `⟨w, by ring⟩`.
-/
theorem exists_eq_pow_mul_unit {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hπ : IsLocalRing.maximalIdeal S = Ideal.span {π}) {x : S} (hx : x ≠ (0 : S)) :
    ∃ (k : ℕ) (u : S), IsUnit u ∧ x = π ^ k * u := by
  classical
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal S)
    (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have hex : ∃ n : ℕ, ¬ (π ^ n ∣ x) := by
    by_contra h0
    have h : ∀ n : ℕ, π ^ n ∣ x := fun n => not_not.mp (not_exists.mp h0 n)
    apply hx
    have hmem : x ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal S ^ n := by
      refine Ideal.mem_iInf.mpr fun n => ?_
      rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact h n
    rw [hK] at hmem
    exact hmem
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have h1 := Nat.find_spec hex
    rw [h0, pow_zero] at h1
    exact h1 (one_dvd x)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hdk : π ^ k ∣ x := by
    have := Nat.find_min hex (show k < Nat.find hex by omega)
    exact not_not.mp this
  obtain ⟨u, rfl⟩ := hdk
  refine ⟨k, u, ?_, rfl⟩
  by_contra hu
  have hum : u ∈ IsLocalRing.maximalIdeal S := (IsLocalRing.mem_maximalIdeal u).mpr hu
  rw [hπ, Ideal.mem_span_singleton] at hum
  obtain ⟨w, rfl⟩ := hum
  apply Nat.find_spec hex
  rw [hk, pow_succ]
  exact ⟨w, by ring⟩

end GlobalTheory.PowMulUnit
