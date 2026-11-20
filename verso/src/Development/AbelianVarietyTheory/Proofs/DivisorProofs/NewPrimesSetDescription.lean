import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

/- English proof (translation)
Establish `hd : 2 * (NumberField.discr D.host.E).natAbs ≠ 0`. Use `NumberField.discr_ne_zero D.host.E` as an intermediate fact. Check the signs of the components of the expression. Simplify using `only [setB, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors, Formalism.MainNotions.WeightThresholdDefs.dE, Nat.lt_succ_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `(⟨h, hp⟩ | ⟨hp, h, _⟩ | h)`. Conclude with `⟨hp, Or.inl ((Nat.le_floor_iff' hp.ne_zero).1 h)⟩`. Conclude with `⟨hp, Or.inr (Or.inl h)⟩`. Conclude with `⟨Y.lev_prime p h, Or.inr (Or.inr h)⟩`. Introduce and unpack `⟨hp, h | h | h⟩`.

Conclude with `Or.inl ⟨(Nat.le_floor_iff' hp.ne_zero).2 h, hp⟩`. Conclude with `Or.inr (Or.inl ⟨hp, h, hd⟩)`. Conclude with `Or.inr (Or.inr h)`.
-/
theorem mem_setB_iff_le {D : D7} (Y : ShimX D.what₂.Tau) (B : ℝ) (p : ℕ) :
    p ∈ setB Y B ↔ p.Prime ∧ ((p : ℝ) ≤ B ∨ p ∣ 2 * dE D ∨ p ∈ Y.lev) := by
  have hd : 2 * (NumberField.discr D.host.E).natAbs ≠ 0 := by
    have := NumberField.discr_ne_zero D.host.E
    positivity
  simp only [setB, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors,
    Formalism.MainNotions.WeightThresholdDefs.dE, Nat.lt_succ_iff]
  constructor
  · rintro (⟨h, hp⟩ | ⟨hp, h, _⟩ | h)
    · exact ⟨hp, Or.inl ((Nat.le_floor_iff' hp.ne_zero).1 h)⟩
    · exact ⟨hp, Or.inr (Or.inl h)⟩
    · exact ⟨Y.lev_prime p h, Or.inr (Or.inr h)⟩
  · rintro ⟨hp, h | h | h⟩
    · exact Or.inl ⟨(Nat.le_floor_iff' hp.ne_zero).2 h, hp⟩
    · exact Or.inr (Or.inl ⟨hp, h, hd⟩)
    · exact Or.inr (Or.inr h)

/- English proof (translation)
Simplify using `only [newPrimes, Finset.mem_sdiff, mem_setB_iff_le]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hp, h⟩, h'⟩`. Establish `h'' : ¬ ((p : ℝ) ≤ B₀ ∨ p ∣ 2 * dE D ∨ p ∈ Y.lev)` using `fun h => h' ⟨hp, h⟩`. Simplify using `only [not_or, not_le] at h''`.

Take `⟨h1, h2, h3⟩` from `h''`. Use `⟨hp, h1, ?_, h2, h3⟩` and prove the remaining obligations. Break down `h with h | h | h` into its components or cases. Conclude with `(Nat.le_floor_iff' hp.ne_zero).2 h`. Conclude with `absurd h h2`.

Conclude with `absurd h h3`. Introduce and unpack `⟨hp, h1, h2, h3, h4⟩`. Use `⟨⟨hp, Or.inl ((Nat.le_floor_iff' hp.ne_zero).1 h2)⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨_, h | h | h⟩`. Conclude with `absurd h (not_le.2 h1)`.

Conclude with `h3 h`. Conclude with `h4 h`.
-/
theorem mem_newPrimes_iff {D : D7} (Y : ShimX D.what₂.Tau) (B₀ B : ℝ) (p : ℕ) :
    p ∈ newPrimes Y B₀ B ↔ p.Prime ∧ B₀ < p ∧ p ≤ ⌊B⌋₊ ∧ ¬ p ∣ 2 * dE D ∧ p ∉ Y.lev := by
  simp only [newPrimes, Finset.mem_sdiff, mem_setB_iff_le]
  constructor
  · rintro ⟨⟨hp, h⟩, h'⟩
    have h'' : ¬ ((p : ℝ) ≤ B₀ ∨ p ∣ 2 * dE D ∨ p ∈ Y.lev) := fun h => h' ⟨hp, h⟩
    simp only [not_or, not_le] at h''
    obtain ⟨h1, h2, h3⟩ := h''
    refine ⟨hp, h1, ?_, h2, h3⟩
    rcases h with h | h | h
    · exact (Nat.le_floor_iff' hp.ne_zero).2 h
    · exact absurd h h2
    · exact absurd h h3
  · rintro ⟨hp, h1, h2, h3, h4⟩
    refine ⟨⟨hp, Or.inl ((Nat.le_floor_iff' hp.ne_zero).1 h2)⟩, ?_⟩
    rintro ⟨_, h | h | h⟩
    · exact absurd h (not_le.2 h1)
    · exact h3 h
    · exact h4 h

/- English proof (translation)
Introduce `D Y B₀ B _`. Use `⟨fun hB p hp => ?_, fun p hp => ((mem_setB_iff_le Y B p).1 hp).1, mem_newPrimes_iff Y B₀ B, fun n => ?_⟩` and prove the remaining obligations. Rewrite `hp`, the goal using `[mem_setB_iff_le]`. Conclude with `⟨hp.1, hp.2.imp_left fun h => h.trans hB⟩`. Use extensionality with `p`.

Simplify using `only [mem_newPrimes_iff, Finset.mem_filter, Finset.mem_range, Nat.floor_natCast, Nat.lt_succ_iff]`. The claim follows by propositional logic.
-/
theorem setB_newP_facts : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ B₀ B : ℝ, 0 ≤ B₀ → (B₀ ≤ B → setB Y B₀ ⊆ setB Y B) ∧ (∀ p ∈ setB Y B, p.Prime) ∧ (∀ p : ℕ, p ∈ newPrimes Y B₀ B ↔ p.Prime ∧ B₀ < p ∧ p ≤ ⌊B⌋₊ ∧ ¬ p ∣ 2 * dE D ∧ p ∉ Y.lev) ∧ ∀ n : ℕ, newPrimes Y B₀ n = (Finset.range (n + 1)).filter (fun p : ℕ => p.Prime ∧ B₀ < (p : ℝ) ∧ ¬ p ∣ 2 * dE D ∧ p ∉ Y.lev) := by
  intro D Y B₀ B _
  refine ⟨fun hB p hp => ?_, fun p hp => ((mem_setB_iff_le Y B p).1 hp).1, mem_newPrimes_iff Y B₀ B, fun n => ?_⟩
  · rw [mem_setB_iff_le] at hp ⊢
    exact ⟨hp.1, hp.2.imp_left fun h => h.trans hB⟩
  · ext p
    simp only [mem_newPrimes_iff, Finset.mem_filter, Finset.mem_range, Nat.floor_natCast, Nat.lt_succ_iff]
    tauto

end GlobalTheory.Mean4
