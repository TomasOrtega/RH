import Mathlib

open NumberField IsDedekindDomain Matrix

namespace Bl.general_b_fact_left_tail

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `hP : (Ideal.span {(g : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime (by exact_mod_cast hg.ne_zero)).2 (Nat.prime_iff_prime_int.mp hg)`. Take `⟨Q, -, hQ, hQc⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 F) (Ideal.span {(g : ℤ)}) ⊥ (by`. Rewrite using `[Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 F)).injective_int]`. Conclude with `bot_le)`. Establish `hgQ : (g : 𝓞 F) ∈ Q`.

Establish `h1 : (g : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 F))`. Rewrite using `[hQc]`. Conclude with `Ideal.subset_span rfl`. Simplify using `using h1`. Use `⟨⟨Q, hQ, ?_⟩, hgQ⟩` and prove the remaining obligations.

Introduce `h`. Rewrite `hgQ` using `[h]`. Establish `h0 : (g : 𝓞 F) = 0` using `(Ideal.mem_bot).1 hgQ`. Conclude with `hg.ne_zero (by exact_mod_cast h0)`.
-/
theorem goal1 (g : ℕ) (hg : g.Prime) : ∃ v : HeightOneSpectrum (𝓞 F), (g : 𝓞 F) ∈ v.asIdeal := by
  have hP : (Ideal.span {(g : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hg.ne_zero)).2 (Nat.prime_iff_prime_int.mp hg)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 F)
    (Ideal.span {(g : ℤ)}) ⊥ (by
      rw [Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 F)).injective_int]
      exact bot_le)
  have hgQ : (g : 𝓞 F) ∈ Q := by
    have h1 : (g : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 F)) := by
      rw [hQc]
      exact Ideal.subset_span rfl
    simpa using h1
  refine ⟨⟨Q, hQ, ?_⟩, hgQ⟩
  intro h
  rw [h] at hgQ
  have h0 : (g : 𝓞 F) = 0 := (Ideal.mem_bot).1 hgQ
  exact hg.ne_zero (by exact_mod_cast h0)

end Bl.general_b_fact_left_tail
