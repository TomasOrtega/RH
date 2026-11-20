import Mathlib
open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise

namespace GlobalTheory.UnramSquare

/- English proof (translation)
Introduce `h p hp hpQ y u hu hyu`. Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Use `haveI hPr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ`. Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `hPr.isMaximal (by simpa using hpZ.ne_zero)`. Use `haveI hQp : Q.IsPrime := inferInstance`.

Use `haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := by`. Use `⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ Q).ne_top ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]`. Simplify using `using hpQ`. Use `letI := Localization.AtPrime.algebraOfLiesOver (Ideal.span {(p : ℤ)}) Q`.

Establish `h2` using `((Algebra.isUnramifiedAt_iff_map_eq ℤ (Ideal.span {(p : ℤ)}) Q).1 h).2`. Establish `hyQ : y ∈ Q` using `hQp.mem_of_pow_mem 2 (by rw [hyu]; exact Q.mul_mem_right _ hpQ)`. Establish `h3 : algebraMap (𝓞 K) (Localization.AtPrime Q) y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)` using `(IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q y).2 hyQ`. Rewrite `h3` using `[← h2, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']`. Take `⟨w, hw⟩` from `h3`.

Take `⟨⟨z, t⟩, hzt⟩` from `IsLocalization.surj Q.primeCompl w`. Establish `htz : (t : 𝓞 K) * y = p * z`. Apply `IsLocalization.injective (Localization.AtPrime Q) Q.primeCompl_le_nonZeroDivisors` to reduce the goal to its premises. Simplify using `only at hzt`. Rewrite using `[map_mul, map_mul, ← hw, ← hzt]`.

Simplify using `only [map_natCast, eq_intCast, Int.cast_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `hp0 : (p : 𝓞 K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `h4 : (t : 𝓞 K) ^ 2 * u = p * z ^ 2`. Apply `mul_left_cancel₀ hp0` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Establish `h5 : (t : 𝓞 K) ^ 2 * u ∈ Q` using `by rw [h4]; exact Q.mul_mem_right _ hpQ`. Break down `hQp.mem_or_mem h5 with h6 | h6` into its components or cases. Conclude with `t.2 (hQp.mem_of_pow_mem 2 h6)`. Conclude with `hu h6`.
-/
theorem not_sq_mul_unit (K : Type) [Field K] [NumberField K] (Q : Ideal (𝓞 K)) [Q.IsMaximal] :
    Algebra.IsUnramifiedAt ℤ Q → ∀ p : ℕ, p.Prime → (p : 𝓞 K) ∈ Q → ∀ y u : 𝓞 K, u ∉ Q →
      y ^ 2 = (p : 𝓞 K) * u → False := by
  intro h p hp hpQ y u hu hyu
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hPr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hPr.isMaximal (by simpa using hpZ.ne_zero)
  haveI hQp : Q.IsPrime := inferInstance
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ Q).ne_top ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using hpQ
  letI := Localization.AtPrime.algebraOfLiesOver (Ideal.span {(p : ℤ)}) Q
  have h2 := ((Algebra.isUnramifiedAt_iff_map_eq ℤ (Ideal.span {(p : ℤ)}) Q).1 h).2
  have hyQ : y ∈ Q := hQp.mem_of_pow_mem 2 (by rw [hyu]; exact Q.mul_mem_right _ hpQ)
  have h3 : algebraMap (𝓞 K) (Localization.AtPrime Q) y ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q y).2 hyQ
  rw [← h2, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at h3
  obtain ⟨w, hw⟩ := h3
  obtain ⟨⟨z, t⟩, hzt⟩ := IsLocalization.surj Q.primeCompl w
  have htz : (t : 𝓞 K) * y = p * z := by
    apply IsLocalization.injective (Localization.AtPrime Q) Q.primeCompl_le_nonZeroDivisors
    simp only at hzt
    rw [map_mul, map_mul, ← hw, ← hzt]
    simp only [map_natCast, eq_intCast, Int.cast_natCast]
    ring
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h4 : (t : 𝓞 K) ^ 2 * u = p * z ^ 2 := by
    apply mul_left_cancel₀ hp0
    calc (p : 𝓞 K) * ((t : 𝓞 K) ^ 2 * u) = (t : 𝓞 K) ^ 2 * y ^ 2 := by rw [hyu]; ring
      _ = ((t : 𝓞 K) * y) ^ 2 := by ring
      _ = p * (p * z ^ 2) := by rw [htz]; ring
  have h5 : (t : 𝓞 K) ^ 2 * u ∈ Q := by rw [h4]; exact Q.mul_mem_right _ hpQ
  rcases hQp.mem_or_mem h5 with h6 | h6
  · exact t.2 (hQp.mem_of_pow_mem 2 h6)
  · exact hu h6

end GlobalTheory.UnramSquare
