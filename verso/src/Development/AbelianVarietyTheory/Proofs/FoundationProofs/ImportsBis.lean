import Mathlib

namespace GlobalTheory.AlgebraicIntegerNormBound

/- English proof (translation)
Introduce `A _ _ Q hQ hQ0 π h1 h2 m hm`. Establish `hP : Prime Q` using `Ideal.prime_of_isPrime hQ0 hQ`. Rewrite `h1`, `h2`, `hm` using `[← Ideal.dvd_span_singleton]`. Take `⟨J, hJ⟩` from `h1`. Establish `hJQ : ¬ Q ∣ J`.

Introduce and unpack `⟨K, hK⟩`. Apply `h2` to reduce the goal to its premises. Conclude with `⟨K, by rw [hJ, hK, pow_two, mul_assoc]⟩`. Rewrite `hm` using `[← Ideal.span_singleton_pow, hJ, mul_pow, pow_succ]`. Establish `hQm : Q ^ m ≠ 0` using `pow_ne_zero _ hQ0`.

Rewrite `hm` using `[mul_dvd_mul_iff_left hQm]`. Conclude with `hJQ (hP.dvd_of_dvd_pow hm)`.
-/
theorem main : ∀ {A : Type} [inst : CommRing A] [IsDedekindDomain A] {Q : Ideal A} [Ideal.IsPrime Q], Q ≠ ⊥ → ∀ {π : A}, π ∈ Q → π ∉ Q ^ (2 : ℕ) → ∀ (m : ℕ), π ^ m ∉ Q ^ (m + (1 : ℕ)) := by
  intro A _ _ Q hQ hQ0 π h1 h2 m hm
  have hP : Prime Q := Ideal.prime_of_isPrime hQ0 hQ
  rw [← Ideal.dvd_span_singleton] at h1 h2 hm
  obtain ⟨J, hJ⟩ := h1
  have hJQ : ¬ Q ∣ J := by
    rintro ⟨K, hK⟩
    apply h2
    exact ⟨K, by rw [hJ, hK, pow_two, mul_assoc]⟩
  rw [← Ideal.span_singleton_pow, hJ, mul_pow, pow_succ] at hm
  have hQm : Q ^ m ≠ 0 := pow_ne_zero _ hQ0
  rw [mul_dvd_mul_iff_left hQm] at hm
  exact hJQ (hP.dvd_of_dvd_pow hm)

end GlobalTheory.AlgebraicIntegerNormBound
