import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.LamOf

/- English proof (translation)
Introduce `N`. Use `⟨fun g g' => ?_, fun j => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [Zls.lamOf, Pi.add_apply]`. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Use function extensionality and compare the values at `i`. Simplify using `only [Zls.lamOf, Zls.omegaVec]`. Rewrite using `[Finset.sum_eq_single j]`.

Distinguish the cases in `h : (i : ℕ) ≤ (j : ℕ)`. Simplify using `[h, Nat.lt_succ_of_le h]`. Establish `h' : ¬ (i : ℕ) < (j : ℕ) + 1` using `fun h2 => h (Nat.le_of_lt_succ h2)`. Simplify using `[h, h']`. Introduce `l _ hl`.

Simplify using `[Pi.single_apply, hl]`. Introduce `hj`. Conclude with `absurd (Finset.mem_univ j) hj`.
-/
theorem lamOf_add_and_single :
    ∀ (N : ℕ), (∀ g g' : Fin (N - 1) → ℕ, Zls.lamOf (g + g') = Zls.lamOf g + Zls.lamOf g') ∧
      ∀ j : Fin (N - 1), Zls.lamOf (Pi.single j 1) = Zls.omegaVec N ((j : ℕ) + 1) := by
  intro N
  refine ⟨fun g g' => ?_, fun j => ?_⟩
  · funext i
    simp only [Zls.lamOf, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  · funext i
    simp only [Zls.lamOf, Zls.omegaVec]
    rw [Finset.sum_eq_single j]
    · by_cases h : (i : ℕ) ≤ (j : ℕ)
      · simp [h, Nat.lt_succ_of_le h]
      · have h' : ¬ (i : ℕ) < (j : ℕ) + 1 := fun h2 => h (Nat.le_of_lt_succ h2)
        simp [h, h']
    · intro l _ hl
      simp [Pi.single_apply, hl]
    · intro hj
      exact absurd (Finset.mem_univ j) hj

end GlobalTheory.CompanionTheory.LamOf
