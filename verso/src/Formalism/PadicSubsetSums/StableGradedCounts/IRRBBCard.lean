import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
import Formalism.GaloisIrreducibility.NoSolvableTransitive

open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `g N hg`. Use `set T : ℕ → Finset ℕ := fun d => (Finset.range (g ^ N + 1)).filter (fun l => l.Prime ∧ g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))) with hT`. Establish `hTd : ∀ d ∈ Finset.Icc 1 N, (T d).card ≤ 3`. Introduce `d hd`. Rewrite `hd` using `[Finset.mem_Icc]`.

Apply `Formalism.GaloisIrreducibility.bbAtMostThree g d (T d) hg hd.1` to reduce the goal to its premises. Introduce `l hl`. Simplify using `only [hT, Finset.mem_filter] at hl`. Conclude with `hl.2.1`. Introduce `l hl`.

Simplify using `only [hT, Finset.mem_filter] at hl`. Establish `h1 : g ^ d < (l ^ padicValNat l (g ^ d - 1)) ^ 4`. Rewrite using `[← pow_mul, mul_comm]`. Conclude with `hl.2.2`. Establish `h2 : ((g : ℝ) ^ ((d : ℝ) / 4)) ^ 4 = (g : ℝ) ^ d`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]`. Establish `: (d : ℝ) / 4 * ((4 : ℕ) : ℝ) = (d : ℝ)` using `by push_cast; ring`. Rewrite using `[this, Real.rpow_natCast]`. Establish `h3 : ((g : ℝ) ^ ((d : ℝ) / 4)) ^ 4 < (((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ)) ^ 4`. Rewrite using `[h2]`.

Conclude with `h1` after adjusting the coercions. Conclude with `lt_of_pow_lt_pow_left₀ 4 (by positivity) h3`. Establish `hsub : (Finset.range (g ^ N + 1)).filter (fun l => l.Prime ∧ ∃ d ∈ Finset.Icc 1 N, g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))) ⊆ (Finset.Icc 1 N).biUnion T`. Introduce `l hl`. Simplify using `only [Finset.mem_filter] at hl`.

Take `⟨hr, hp, d, hd, hlt⟩` from `hl`. Rewrite using `[Finset.mem_biUnion]`. Conclude with `⟨d, hd, by simp only [hT, Finset.mem_filter]; exact ⟨hr, hp, hlt⟩⟩`. Establish `hcard : ((Finset.Icc 1 N).biUnion T).card ≤ 3 * N`. Combine the equalities or inequalities in the displayed calculation.

Unfold `BB`. Combine the equalities or inequalities in the displayed calculation. Use `(Finset.card_le_card hsub).trans hcard` as an intermediate fact. Use `Nat.add_le_add_right this 1` and compare the differences between its conclusion and the goal.
-/
theorem bad_primes_cardinality : BBCard := by
  classical
  intro g N hg
  set T : ℕ → Finset ℕ := fun d => (Finset.range (g ^ N + 1)).filter (fun l =>
    l.Prime ∧ g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))) with hT
  have hTd : ∀ d ∈ Finset.Icc 1 N, (T d).card ≤ 3 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    apply Formalism.GaloisIrreducibility.bbAtMostThree g d (T d) hg hd.1
    · intro l hl
      simp only [hT, Finset.mem_filter] at hl
      exact hl.2.1
    · intro l hl
      simp only [hT, Finset.mem_filter] at hl
      have h1 : g ^ d < (l ^ padicValNat l (g ^ d - 1)) ^ 4 := by
        rw [← pow_mul, mul_comm]; exact hl.2.2
      have h2 : ((g : ℝ) ^ ((d : ℝ) / 4)) ^ 4 = (g : ℝ) ^ d := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        have : (d : ℝ) / 4 * ((4 : ℕ) : ℝ) = (d : ℝ) := by push_cast; ring
        rw [this, Real.rpow_natCast]
      have h3 : ((g : ℝ) ^ ((d : ℝ) / 4)) ^ 4 <
          (((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ)) ^ 4 := by
        rw [h2]; exact_mod_cast h1
      exact lt_of_pow_lt_pow_left₀ 4 (by positivity) h3
  have hsub : (Finset.range (g ^ N + 1)).filter (fun l =>
      l.Prime ∧ ∃ d ∈ Finset.Icc 1 N, g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))) ⊆
      (Finset.Icc 1 N).biUnion T := by
    intro l hl
    simp only [Finset.mem_filter] at hl
    obtain ⟨hr, hp, d, hd, hlt⟩ := hl
    rw [Finset.mem_biUnion]
    exact ⟨d, hd, by simp only [hT, Finset.mem_filter]; exact ⟨hr, hp, hlt⟩⟩
  have hcard : ((Finset.Icc 1 N).biUnion T).card ≤ 3 * N := by
    calc ((Finset.Icc 1 N).biUnion T).card ≤ ∑ d ∈ Finset.Icc 1 N, (T d).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _d ∈ Finset.Icc 1 N, 3 := Finset.sum_le_sum hTd
      _ = 3 * N := by simp [mul_comm]
  unfold BB
  calc _ ≤ _ + 1 := Finset.card_insert_le _ _
    _ ≤ 3 * N + 1 := by
      have := (Finset.card_le_card hsub).trans hcard
      convert Nat.add_le_add_right this 1

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
