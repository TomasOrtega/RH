import Mathlib

universe u_1

namespace GlobalTheory.PrimeDivisorMembership

/- English proof (translation)
Introduce `R _ P hP n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn hmem`. Distinguish the cases in `h1 : n = 1`.

Substitute `h1` using the available equality. Rewrite `hmem` using `[Nat.cast_one]`. Conclude with `absurd ((Ideal.eq_top_iff_one P).2 hmem) hP.ne_top`. Establish `hmin` using `Nat.minFac_prime h1`. Take `⟨m, hm⟩` from `Nat.minFac_dvd n`.

Establish `hmem' : (n.minFac : R) * (m : R) ∈ P`. Rewrite using `[← Nat.cast_mul, ← hm]`. Conclude with `hmem`. Break down `hP.mem_or_mem hmem' with hq | hq` into its components or cases. Conclude with `⟨n.minFac, hmin, Nat.minFac_dvd n, hq⟩`.

Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Rewrite `hm` using `[mul_zero]`. Conclude with `hn hm`. Establish `hlt : m < n`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨q, hq1, hq2, hq3⟩` from `ih m hlt hm0 hq`. Conclude with `⟨q, hq1, hq2.trans (Dvd.intro_left _ hm.symm), hq3⟩`.
-/
theorem exists_prime_dvd_mem : ∀ {R : Type u_1} [inst : CommRing R] (P : Ideal R), Ideal.IsPrime P → ∀ (n : ℕ), n ≠ (0 : ℕ) → (↑n : R) ∈ P → ∃ (q : ℕ), Nat.Prime q ∧ q ∣ n ∧ (↑q : R) ∈ P := by
  intro R _ P hP n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    by_cases h1 : n = 1
    · subst h1
      rw [Nat.cast_one] at hmem
      exact absurd ((Ideal.eq_top_iff_one P).2 hmem) hP.ne_top
    · have hmin := Nat.minFac_prime h1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hmem' : (n.minFac : R) * (m : R) ∈ P := by
        rw [← Nat.cast_mul, ← hm]
        exact hmem
      rcases hP.mem_or_mem hmem' with hq | hq
      · exact ⟨n.minFac, hmin, Nat.minFac_dvd n, hq⟩
      · have hm0 : m ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hm
          exact hn hm
        have hlt : m < n := by
          calc m < 2 * m := by omega
            _ ≤ n.minFac * m := Nat.mul_le_mul_right _ hmin.two_le
            _ = n := hm.symm
        obtain ⟨q, hq1, hq2, hq3⟩ := ih m hlt hm0 hq
        exact ⟨q, hq1, hq2.trans (Dvd.intro_left _ hm.symm), hq3⟩

end GlobalTheory.PrimeDivisorMembership
