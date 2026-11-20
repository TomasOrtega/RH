import Mathlib
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `ℓ _ S _ _ s hs`. Set `B` to `integralClosure ℤ_[ℓ] S`. Set `b : B` to `⟨s, hs⟩`. Establish `hu : IsUnit (1 + (ℓ : B) * b)`. Assume the negation of the conclusion as `hn`.

Take `⟨M, hM, hmem⟩` from `exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hn)`. Establish `hmax : (M.comap (algebraMap ℤ_[ℓ] B)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M`. Establish `heq` using `IsLocalRing.eq_maximalIdeal hmax`. Establish `hl : (ℓ : ℤ_[ℓ]) ∈ M.comap (algebraMap ℤ_[ℓ] B)`. Rewrite using `[heq, PadicInt.maximalIdeal_eq_span_p]`.

Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `hl` using `[Ideal.mem_comap, map_natCast]`. Establish `h1 : (1 : B) ∈ M`. Use `M.sub_mem hmem (M.mul_mem_right b hl)` as an intermediate fact. Simplify using `using this`.

Conclude with `hM.ne_top ((Ideal.eq_top_iff_one M).mpr h1)`. Take `⟨r, hr⟩` from `hu.exists_right_inv`. Use `⟨(r : S), ?_, r.2⟩` and prove the remaining obligations. Use `congrArg (fun x : B => (x : S)) hr` as an intermediate fact. Simplify `this` using `[b]`.
-/
theorem exists_integral_inv_one_add_prime_mul :
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S] (s : S),
      IsIntegral ℤ_[ℓ] s → ∃ r : S, (1 + (ℓ : S) * s) * r = 1 ∧ IsIntegral ℤ_[ℓ] r := by
  intro ℓ _ S _ _ s hs
  let B := integralClosure ℤ_[ℓ] S
  let b : B := ⟨s, hs⟩
  have hu : IsUnit (1 + (ℓ : B) * b) := by
    by_contra hn
    obtain ⟨M, hM, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hn)
    have hmax : (M.comap (algebraMap ℤ_[ℓ] B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have heq := IsLocalRing.eq_maximalIdeal hmax
    have hl : (ℓ : ℤ_[ℓ]) ∈ M.comap (algebraMap ℤ_[ℓ] B) := by
      rw [heq, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at hl
    have h1 : (1 : B) ∈ M := by
      have := M.sub_mem hmem (M.mul_mem_right b hl)
      simpa using this
    exact hM.ne_top ((Ideal.eq_top_iff_one M).mpr h1)
  obtain ⟨r, hr⟩ := hu.exists_right_inv
  refine ⟨(r : S), ?_, r.2⟩
  have := congrArg (fun x : B => (x : S)) hr
  simpa [b] using this

end GlobalTheory
