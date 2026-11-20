import Mathlib

namespace GlobalTheory.IsolatedTheoremFour

open IsDedekindDomain

/- English proof (translation)
Introduce `K _ _ l hl`. Establish `hp : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.mp hl`. Establish `hmax : (Ideal.span {(l : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible`. Establish `hker : RingHom.ker (algebraMap ℤ (NumberField.RingOfIntegers K)) ≤ Ideal.span {(l : ℤ)}`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).mp (RingHom.injective_int (algebraMap ℤ (NumberField.RingOfIntegers K)))]`.

Conclude with `bot_le`. Take `⟨Q, hQ, hQc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (Ideal.span {(l : ℤ)}) hker`. Establish `hlQ : ((l : ℕ) : NumberField.RingOfIntegers K) ∈ Q`. Establish `h1 : (l : ℤ) ∈ Q.comap (algebraMap ℤ (NumberField.RingOfIntegers K))`. Rewrite using `[hQc]`.

Conclude with `Ideal.subset_span rfl`. Simplify using `using h1`. Establish `hl0 : ((l : ℕ) : NumberField.RingOfIntegers K) ≠ 0`. Conclude with `hl.ne_zero` after adjusting the coercions. Conclude with `⟨⟨Q, hQ.isPrime, fun h => hl0 (Ideal.mem_bot.mp (h ▸ hlQ))⟩, hlQ⟩`.
-/
theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] {l : ℕ}, Nat.Prime l → ∃ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), (↑l : NumberField.RingOfIntegers K) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v := by
  intro K _ _ l hl
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hker : RingHom.ker (algebraMap ℤ (NumberField.RingOfIntegers K)) ≤ Ideal.span {(l : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (RingHom.injective_int (algebraMap ℤ (NumberField.RingOfIntegers K)))]
    exact bot_le
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (Ideal.span {(l : ℤ)}) hker
  have hlQ : ((l : ℕ) : NumberField.RingOfIntegers K) ∈ Q := by
    have h1 : (l : ℤ) ∈ Q.comap (algebraMap ℤ (NumberField.RingOfIntegers K)) := by
      rw [hQc]
      exact Ideal.subset_span rfl
    simpa using h1
  have hl0 : ((l : ℕ) : NumberField.RingOfIntegers K) ≠ 0 := by
    exact_mod_cast hl.ne_zero
  exact ⟨⟨Q, hQ.isPrime, fun h => hl0 (Ideal.mem_bot.mp (h ▸ hlQ))⟩, hlQ⟩

end GlobalTheory.IsolatedTheoremFour
