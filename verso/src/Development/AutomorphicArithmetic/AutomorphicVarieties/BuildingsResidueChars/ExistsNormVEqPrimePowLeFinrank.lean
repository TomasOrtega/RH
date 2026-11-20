import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

/- English proof (translation)
Introduce `K _ _ p w hp hpw`. Establish `hcard : normV w = Ideal.absNorm w.asIdeal`. Unfold `normV`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hspan : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ Module.finrank ℚ K`.

Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `e : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ)` using `by simp`. Rewrite using `[e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]`. Simplify using `[Int.natAbs_pow]`. Establish `hdvd : Ideal.absNorm w.asIdeal ∣ p ^ Module.finrank ℚ K`.

Rewrite using `[← hspan]`. Conclude with `Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hpw)`. Take `⟨h, hle, heq⟩` from `(Nat.dvd_prime_pow hp).mp hdvd`. Use `⟨h, ?_, hle, hcard.trans heq⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos h with h0 | h0` into its components or cases.

It suffices to derive a contradiction. Rewrite `heq` using `[h0, pow_zero, Ideal.absNorm_eq_one_iff]`. Conclude with `w.isPrime.ne_top heq`. Conclude with `h0`.
-/
theorem UpperTheory.exists_normV_eq_prime_pow_le_finrank :
    ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ∃ h : ℕ, 1 ≤ h ∧ h ≤ Module.finrank ℚ K ∧ normV w = p ^ h := by
  intro K _ _ p w hp hpw
  have hcard : normV w = Ideal.absNorm w.asIdeal := by
    unfold normV
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hspan : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have e : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have hdvd : Ideal.absNorm w.asIdeal ∣ p ^ Module.finrank ℚ K := by
    rw [← hspan]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hpw)
  obtain ⟨h, hle, heq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨h, ?_, hle, hcard.trans heq⟩
  rcases Nat.eq_zero_or_pos h with h0 | h0
  · exfalso
    rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at heq
    exact w.isPrime.ne_top heq
  · exact h0
