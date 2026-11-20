import Mathlib

namespace GlobalTheory.AlgebraicIntegerNormBound

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Supply the required witnesses or components. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
