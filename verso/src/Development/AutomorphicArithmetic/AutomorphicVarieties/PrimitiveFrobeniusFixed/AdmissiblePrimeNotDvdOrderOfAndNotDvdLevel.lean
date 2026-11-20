import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Introduce `l F r d _ hl hr hrF hd`. Take `⟨hsq, hq⟩` from `hd`. Establish `hone : ∀ p : ℕ, p.Prime → p ≡ 1 [MOD F] → ¬ p ∣ F` using `fun p hp h hpF => by`. Establish `h1 : p ≡ 1 [MOD p]` using `h.of_dvd hpF`. Establish `h2 : p ∣ 1` using `(h1.dvd_iff dvd_rfl).1 dvd_rfl`.

Conclude with `hp.one_lt.ne' (Nat.dvd_one.1 h2)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `set n := ∏ q ∈ d.primeFactors, orderOf (r : ZMod q) with hn`. Establish `hln : ¬ l ∣ n`. Introduce `h`.

Take `⟨q, hqm, hlq⟩` from `(Prime.dvd_finset_prod_iff hl.prime _).1 h`. Conclude with `(hq q (Nat.prime_of_mem_primeFactors hqm) (Nat.dvd_of_mem_primeFactors hqm)).2.2.2 hlq`. Establish `hcop : Nat.Coprime F d`. Apply `Nat.coprime_of_dvd` to reduce the goal to its premises. Introduce `k hk hkF hkd`.

Conclude with `hone k hk (hq k hk hkd).2.1 hkF`. Establish `hpos : 1 ≤ r ^ n` using `Nat.one_le_pow _ _ hr.pos`. Establish `hF : r ^ n ≡ 1 [MOD F]` using `by simpa using hrF.pow n`. Establish `hD : r ^ n ≡ 1 [MOD d]`. Establish `h1 : ∏ q ∈ d.primeFactors, q ∣ r ^ n - 1`.

Apply `Finset.prod_primes_dvd` to reduce the goal to its premises. Introduce `a ha`. Conclude with `(Nat.prime_of_mem_primeFactors ha).prime`. Introduce `a ha`. Establish `h2 : (r : ZMod a) ^ n = 1` using `orderOf_dvd_iff_pow_eq_one.1 (Finset.dvd_prod_of_mem (fun q : ℕ => orderOf (r : ZMod q)) ha)`.

Establish `h3 : r ^ n ≡ 1 [MOD a]`. Rewrite using `[← ZMod.natCast_eq_natCast_iff]`. Simplify using `using h2`. Conclude with `(Nat.modEq_iff_dvd' hpos).1 h3.symm`. Rewrite `h1` using `[Nat.prod_primeFactors_of_squarefree hsq]`.

Conclude with `((Nat.modEq_iff_dvd' hpos).2 h1).symm`. Establish `hFD : r ^ n ≡ 1 [MOD F * d]` using `(Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hF, hD⟩`. Establish `h4 : (r : ZMod (F * d)) ^ n = 1`. Use `(ZMod.natCast_eq_natCast_iff _ _ _).2 hFD` as an intermediate fact. Simplify using `using this`.

Conclude with `fun h => hln (h.trans (orderOf_dvd_of_pow_eq_one h4))`. Introduce `h`. Break down `(Nat.Prime.dvd_mul hr).1 h with h | h` into its components or cases. Conclude with `hone r hr hrF h`. Conclude with `(hq r hr h).2.2.1 rfl`.
-/
theorem UpperTheory.admissible_prime_not_dvd_orderOf_and_not_dvd_level :
    ∀ (l F r d : ℕ), F ≠ 0 → l.Prime → r.Prime → r ≡ 1 [MOD F] → ML.admitted l F r d → ¬ l ∣ orderOf (r : ZMod (F * d)) ∧ ¬ r ∣ F * d := by
  intro l F r d _ hl hr hrF hd
  obtain ⟨hsq, hq⟩ := hd
  have hone : ∀ p : ℕ, p.Prime → p ≡ 1 [MOD F] → ¬ p ∣ F := fun p hp h hpF => by
    have h1 : p ≡ 1 [MOD p] := h.of_dvd hpF
    have h2 : p ∣ 1 := (h1.dvd_iff dvd_rfl).1 dvd_rfl
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  refine ⟨?_, ?_⟩
  · set n := ∏ q ∈ d.primeFactors, orderOf (r : ZMod q) with hn
    have hln : ¬ l ∣ n := by
      intro h
      obtain ⟨q, hqm, hlq⟩ := (Prime.dvd_finset_prod_iff hl.prime _).1 h
      exact (hq q (Nat.prime_of_mem_primeFactors hqm) (Nat.dvd_of_mem_primeFactors hqm)).2.2.2 hlq
    have hcop : Nat.Coprime F d := by
      apply Nat.coprime_of_dvd
      intro k hk hkF hkd
      exact hone k hk (hq k hk hkd).2.1 hkF
    have hpos : 1 ≤ r ^ n := Nat.one_le_pow _ _ hr.pos
    have hF : r ^ n ≡ 1 [MOD F] := by simpa using hrF.pow n
    have hD : r ^ n ≡ 1 [MOD d] := by
      have h1 : ∏ q ∈ d.primeFactors, q ∣ r ^ n - 1 := by
        apply Finset.prod_primes_dvd
        · intro a ha
          exact (Nat.prime_of_mem_primeFactors ha).prime
        · intro a ha
          have h2 : (r : ZMod a) ^ n = 1 :=
            orderOf_dvd_iff_pow_eq_one.1 (Finset.dvd_prod_of_mem (fun q : ℕ => orderOf (r : ZMod q)) ha)
          have h3 : r ^ n ≡ 1 [MOD a] := by
            rw [← ZMod.natCast_eq_natCast_iff]
            simpa using h2
          exact (Nat.modEq_iff_dvd' hpos).1 h3.symm
      rw [Nat.prod_primeFactors_of_squarefree hsq] at h1
      exact ((Nat.modEq_iff_dvd' hpos).2 h1).symm
    have hFD : r ^ n ≡ 1 [MOD F * d] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hF, hD⟩
    have h4 : (r : ZMod (F * d)) ^ n = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hFD
      simpa using this
    exact fun h => hln (h.trans (orderOf_dvd_of_pow_eq_one h4))
  · intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact hone r hr hrF h
    · exact (hq r hr h).2.2.1 rfl
