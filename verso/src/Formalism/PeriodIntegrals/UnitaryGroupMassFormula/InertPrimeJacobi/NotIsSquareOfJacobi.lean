import Mathlib
import Formalism.PeriodIntegrals.InertPrime

open NumberField

namespace PI.InertPrimeWork

/- English proof (translation)
Use `haveI := Fact.mk hp`. Rewrite `h` using `[← jacobiSym.legendreSym.to_jacobiSym]`. Conclude with `(legendreSym.eq_neg_one_iff p).1 h`.
-/
theorem not_isSquare_of_jacobi {d p : ℕ} (hp : p.Prime) (h : jacobiSym (-(d : ℤ)) p = -1) :
    ¬ IsSquare (((-(d : ℤ) : ℤ)) : ZMod p) := by
  haveI := Fact.mk hp
  rw [← jacobiSym.legendreSym.to_jacobiSym] at h
  exact (legendreSym.eq_neg_one_iff p).1 h

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `hsq` using `not_isSquare_of_jacobi hp hj`. Establish `hnormI : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2`. Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `e : ((p : 𝓞 K)) = algebraMap ℤ (𝓞 K) (p : ℤ)` using `by simp`.

Rewrite using `[e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, hK]`. Simplify using the standard rewrite rules. Establish `hp1 : p ^ 2 ≠ 1`. Use `hp.one_lt` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hIne : Ideal.span {(p : 𝓞 K)} ≠ ⊤`. Introduce `h`. Rewrite `hnormI` using `[h, Ideal.absNorm_top]`. Conclude with `hp1 hnormI.symm`. Take `⟨P, hPmax, hIP⟩` from `Ideal.exists_le_maximal _ hIne`.

Establish `hdvd : Ideal.absNorm P ∣ p ^ 2` using `hnormI ▸ Ideal.absNorm_dvd_absNorm_of_le hIP`. Take `⟨k, hk, hPk⟩` from `(Nat.dvd_prime_pow hp).1 hdvd`. Use `interval_cases k`. Rewrite `hPk` using `[pow_zero, Ideal.absNorm_eq_one_iff]`. Conclude with `absurd hPk hPmax.ne_top`.

It suffices to derive a contradiction. Rewrite `hPk` using `[pow_one]`. Establish `hP0 : P ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hPk` using `[Ideal.absNorm_bot]`.

Conclude with `hp.ne_zero hPk.symm`. Use `haveI : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0`. Use `letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _`. Use `letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P`. Establish `hcard : Fintype.card (𝓞 K ⧸ P) = p`.

Rewrite using `[Fintype.card_eq_nat_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hPk]`. Use `haveI : CharP (𝓞 K ⧸ P) p := charP_of_card_eq_prime hcard`. Set `ψ : ZMod p →+* 𝓞 K ⧸ P` to `ZMod.castHom (dvd_refl p) _`. Establish `hψi : Function.Injective ψ` using `ψ.injective`. Establish `hψb : Function.Bijective ψ` using `(Fintype.bijective_iff_injective_and_card ψ).2 ⟨hψi, by rw [ZMod.card, hcard]⟩`.

Establish `hbi : IsIntegral ℤ b`. Use `⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩` and prove the remaining obligations. Conclude with `Polynomial.monic_X_pow_add_C _ two_ne_zero`. Simplify using `[Polynomial.eval₂_add, hb]`. Set `β : 𝓞 K` to `⟨b, hbi⟩`.

Establish `hβ : β ^ 2 = -(d : 𝓞 K)`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Use `push_cast`. Conclude with `hb`. Take `⟨t, ht⟩` from `hψb.2 (Ideal.Quotient.mk P β)`.

Apply `hsq` to reduce the goal to its premises. Use `⟨t, ?_⟩` and prove the remaining obligations. Apply `hψi` to reduce the goal to its premises. Rewrite using `[map_mul, ← sq, ht, ← map_pow, hβ]`. Use `push_cast`.

Simplify using the standard rewrite rules. Rewrite `hPk` using `[← hnormI]`. Establish `hPI : P ∣ Ideal.span {(p : 𝓞 K)}` using `Ideal.dvd_iff_le.2 hIP`. Take `⟨J, hJ⟩` from `hPI`. Establish `hJ1 : Ideal.absNorm J = 1`.

Establish `h2` using `congrArg Ideal.absNorm hJ`. Rewrite `h2` using `[map_mul, hPk]`. Establish `hpos : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) ≠ 0`. Rewrite using `[hnormI]`. Conclude with `pow_ne_zero _ hp.ne_zero`.

Conclude with `(Nat.mul_eq_left hpos).1 h2.symm`. Rewrite `hJ1` using `[Ideal.absNorm_eq_one_iff]`. Rewrite using `[hJ, hJ1, Ideal.mul_top]`. Conclude with `hPmax.isPrime`.
-/
theorem inert (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (b : K) (d p : ℕ)
    (hb : b ^ 2 = -(d : K)) (hp : p.Prime) (hj : jacobiSym (-(d : ℤ)) p = -1) :
    (Ideal.span {(p : 𝓞 K)}).IsPrime := by
  haveI := Fact.mk hp
  have hsq := not_isSquare_of_jacobi hp hj
  have hnormI : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_singleton]
    have e : ((p : 𝓞 K)) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, hK]
    simp
  have hp1 : p ^ 2 ≠ 1 := by
    have := hp.one_lt
    nlinarith
  have hIne : Ideal.span {(p : 𝓞 K)} ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at hnormI
    exact hp1 hnormI.symm
  obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal _ hIne
  have hdvd : Ideal.absNorm P ∣ p ^ 2 := hnormI ▸ Ideal.absNorm_dvd_absNorm_of_le hIP
  obtain ⟨k, hk, hPk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  interval_cases k
  · rw [pow_zero, Ideal.absNorm_eq_one_iff] at hPk
    exact absurd hPk hPmax.ne_top
  · exfalso
    rw [pow_one] at hPk
    have hP0 : P ≠ ⊥ := by
      rintro rfl
      rw [Ideal.absNorm_bot] at hPk
      exact hp.ne_zero hPk.symm
    haveI : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
    letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    have hcard : Fintype.card (𝓞 K ⧸ P) = p := by
      rw [Fintype.card_eq_nat_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hPk]
    haveI : CharP (𝓞 K ⧸ P) p := charP_of_card_eq_prime hcard
    let ψ : ZMod p →+* 𝓞 K ⧸ P := ZMod.castHom (dvd_refl p) _
    have hψi : Function.Injective ψ := ψ.injective
    have hψb : Function.Bijective ψ :=
      (Fintype.bijective_iff_injective_and_card ψ).2 ⟨hψi, by rw [ZMod.card, hcard]⟩
    have hbi : IsIntegral ℤ b := by
      refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
      · exact Polynomial.monic_X_pow_add_C _ two_ne_zero
      · simp [Polynomial.eval₂_add, hb]
    let β : 𝓞 K := ⟨b, hbi⟩
    have hβ : β ^ 2 = -(d : 𝓞 K) := by
      apply RingOfIntegers.coe_injective
      push_cast
      exact hb
    obtain ⟨t, ht⟩ := hψb.2 (Ideal.Quotient.mk P β)
    apply hsq
    refine ⟨t, ?_⟩
    apply hψi
    rw [map_mul, ← sq, ht, ← map_pow, hβ]
    push_cast
    simp
  · rw [← hnormI] at hPk
    have hPI : P ∣ Ideal.span {(p : 𝓞 K)} := Ideal.dvd_iff_le.2 hIP
    obtain ⟨J, hJ⟩ := hPI
    have hJ1 : Ideal.absNorm J = 1 := by
      have h2 := congrArg Ideal.absNorm hJ
      rw [map_mul, hPk] at h2
      have hpos : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) ≠ 0 := by
        rw [hnormI]
        exact pow_ne_zero _ hp.ne_zero
      exact (Nat.mul_eq_left hpos).1 h2.symm
    rw [Ideal.absNorm_eq_one_iff] at hJ1
    rw [hJ, hJ1, Ideal.mul_top]
    exact hPmax.isPrime

end PI.InertPrimeWork
