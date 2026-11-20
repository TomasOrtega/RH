import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsPrimitiveRootTorsionOrder
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuBasic
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TotientLeOfCycPowEqOne
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuSumApprox
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuLe
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuQDUnit

open NumberField Formalism.HC KStar.Tree

/- English proof (translation)
Rewrite using `[Real.log_nat_eq_sum_factorization, Finsupp.sum]`. Combine the equalities or inequalities in the displayed calculation. Use `(Finset.sum_filter_of_ne ?_).symm` and prove the remaining obligations. Introduce `l _ h`. Assume the negation of the conclusion as `hs`.

Rewrite `h` using `[Finsupp.notMem_support_iff.mp hs]`. Simplify using `at h`. Use `_ ≤ ∑ l ∈ m.factorization.support, (m.factorization l : ℝ) * Real.log l := by`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `l hl`.

Conclude with `(Finset.mem_filter.mp hl).2`. Introduce `l hl _`. Establish `hp : l.Prime` using `Nat.prime_of_mem_primeFactors (by simpa using hl)`. Apply `mul_nonneg (Nat.cast_nonneg _)` to reduce the goal to its premises. Conclude with `Real.log_nonneg (by exact_mod_cast hp.one_lt.le)`.
-/
private theorem sum_factorization_mul_log_le (m : ℕ) (S : Finset ℕ) :
    ∑ l ∈ S, (m.factorization l : ℝ) * Real.log l ≤ Real.log m := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ l ∈ S, (m.factorization l : ℝ) * Real.log l
      = ∑ l ∈ S.filter (· ∈ m.factorization.support), (m.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_filter_of_ne ?_).symm
        intro l _ h
        by_contra hs
        rw [Finsupp.notMem_support_iff.mp hs] at h
        simp at h
    _ ≤ ∑ l ∈ m.factorization.support, (m.factorization l : ℝ) * Real.log l := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro l hl
          exact (Finset.mem_filter.mp hl).2
        · intro l hl _
          have hp : l.Prime := Nat.prime_of_mem_primeFactors (by simpa using hl)
          apply mul_nonneg (Nat.cast_nonneg _)
          exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)

/- English proof (translation)
Introduce `φ H Ω _ _ _ n hn hq hd ν hν S hS`. Establish `key : ∀ l ∈ S, (ν l : ℝ) * Real.log l ≤ (H.QS.factorization l : ℝ) * Real.log l + (n.factorization l : ℝ) * Real.log l`. Introduce `l hl`. Establish `hp : l.Prime` using `hS l hl`. Use `haveI : Fact l.Prime := ⟨hp⟩`.

Establish `hlog : 0 ≤ Real.log l` using `Real.log_nonneg (by exact_mod_cast hp.one_lt.le)`. Establish `hnat : ν l ≤ H.QS.factorization l + n.factorization l`. Rewrite using `[hν l]`. Distinguish the cases in `hlq : l = H.q`. Rewrite using `[UpperTheory.Mu.nuQD φ H l Ω n (Or.inl hlq) (hlq ▸ hq)]`.

Conclude with `Nat.zero_le _`. Distinguish the cases in `hld : l = H.d`. Rewrite using `[UpperTheory.Mu.nuQD φ H l Ω n (Or.inr hld) (hld ▸ hd)]`. Conclude with `Nat.zero_le _`. Use `UpperTheory.Mu.nuLe φ H l Ω n hn hlq hld` as an intermediate fact.

Apply the tactic sequence `split_ifs at this <;> omega`. Rewrite using `[← add_mul]`. Apply `mul_le_mul_of_nonneg_right _ hlog` to reduce the goal to its premises. Conclude with `hnat` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.Mu.nuSum :
    ∀ (φ : Frame) (H : HostRaw φ) (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (n : ℕ), Odd n → ¬ (H.q - 1) / 2 ∣ n → ¬ (H.d - 1) / 2 ∣ n → ∀ ν : ℕ → ℕ, (∀ (l : ℕ) [Fact l.Prime], ν l = nuOf l (cyc l H.E Ω) n) → ∀ S : Finset ℕ, (∀ l ∈ S, l.Prime) → ∑ l ∈ S, (ν l : ℝ) * Real.log l ≤ Real.log H.QS + Real.log n := by
  intro φ H Ω _ _ _ n hn hq hd ν hν S hS
  have key : ∀ l ∈ S, (ν l : ℝ) * Real.log l ≤
      (H.QS.factorization l : ℝ) * Real.log l + (n.factorization l : ℝ) * Real.log l := by
    intro l hl
    have hp : l.Prime := hS l hl
    haveI : Fact l.Prime := ⟨hp⟩
    have hlog : 0 ≤ Real.log l := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have hnat : ν l ≤ H.QS.factorization l + n.factorization l := by
      rw [hν l]
      by_cases hlq : l = H.q
      · rw [UpperTheory.Mu.nuQD φ H l Ω n (Or.inl hlq) (hlq ▸ hq)]
        exact Nat.zero_le _
      by_cases hld : l = H.d
      · rw [UpperTheory.Mu.nuQD φ H l Ω n (Or.inr hld) (hld ▸ hd)]
        exact Nat.zero_le _
      have := UpperTheory.Mu.nuLe φ H l Ω n hn hlq hld
      split_ifs at this <;> omega
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ hlog
    exact_mod_cast hnat
  calc ∑ l ∈ S, (ν l : ℝ) * Real.log l
      ≤ ∑ l ∈ S, ((H.QS.factorization l : ℝ) * Real.log l + (n.factorization l : ℝ) * Real.log l) :=
        Finset.sum_le_sum key
    _ = ∑ l ∈ S, (H.QS.factorization l : ℝ) * Real.log l + ∑ l ∈ S, (n.factorization l : ℝ) * Real.log l :=
        Finset.sum_add_distrib
    _ ≤ Real.log H.QS + Real.log n :=
        add_le_add (sum_factorization_mul_log_le H.QS S) (sum_factorization_mul_log_le n S)
