import Mathlib

namespace GlobalTheory.PrimeInHeightOneSpectrum

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn hmem`. Establish `h1 : n ≠ 1`.

Introduce and unpack `rfl`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one P).mpr (by simpa using hmem))`. Establish `hpr : Nat.Prime n.minFac` using `Nat.minFac_prime h1`. Take `⟨m, hm⟩` from `Nat.minFac_dvd n`. Establish `hmul : ((n.minFac : R) * (m : R)) ∈ P`.

Rewrite using `[← Nat.cast_mul, ← hm]`. Conclude with `hmem`. Break down `hP.mem_or_mem hmul with h | h` into its components or cases. Conclude with `⟨_, hpr, h⟩`. Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at hm; exact hn hm`.

Establish `hlt : m < n`. Rewrite using `[hm]`. Use `hpr.two_le` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Conclude with `ih m hlt hm0 h`.
-/
theorem exists_prime_natCast_mem {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, Nat.Prime p ∧ (p : R) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    have h1 : n ≠ 1 := by
      rintro rfl
      exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr (by simpa using hmem))
    have hpr : Nat.Prime n.minFac := Nat.minFac_prime h1
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    have hmul : ((n.minFac : R) * (m : R)) ∈ P := by
      rw [← Nat.cast_mul, ← hm]; exact hmem
    rcases hP.mem_or_mem hmul with h | h
    · exact ⟨_, hpr, h⟩
    · have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hn hm
      have hlt : m < n := by
        rw [hm]
        have := hpr.two_le
        calc m = 1 * m := (one_mul m).symm
          _ < n.minFac * m := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hm0)
      exact ih m hlt hm0 h

/- English proof (translation)
Use `haveI := v.isPrime`. Conclude with `exists_prime_natCast_mem v.asIdeal (Ideal.absNorm v.asIdeal) (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot) (Ideal.absNorm_mem _)`.
-/
theorem exists_prime_mem_heightOneSpectrum {K : Type} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v := by
  haveI := v.isPrime
  exact exists_prime_natCast_mem v.asIdeal (Ideal.absNorm v.asIdeal)
    (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot) (Ideal.absNorm_mem _)

/- English proof (translation)
Introduce `v` and use `exists_prime_mem_heightOneSpectrum v`.
-/
theorem target : ∀ {K : Type} [inst : Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v :=
  fun v => exists_prime_mem_heightOneSpectrum v

end GlobalTheory.PrimeInHeightOneSpectrum
