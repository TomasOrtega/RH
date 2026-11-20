import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Imports

open Finset

namespace GlobalTheory.WigSh

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem wigner_den_ne_zero {n : ℕ} (L : Fin (n+1) → ℤ) (l : Fin (n+1)) (hL : StrictAnti L) :
    (∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  have h1 : j ≠ l := (Finset.mem_erase.mp hj).1
  have h2 : L j ≠ L l := fun h => h1 (hL.injective h)
  exact sub_ne_zero.mpr (by exact_mod_cast h2)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem wigner_extreme_ne_zero : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (l : Fin (n+1)), StrictAnti L → ((∀ j, L j ≠ L l + 1) → GlobalTheory.WigSh.wP L (fun j : Fin n => L j.castSucc) l ≠ 0) ∧ ((∀ j, L j ≠ L l - 1) → GlobalTheory.WigSh.wM L (fun j : Fin n => L j.succ + 1) l ≠ 0) := by
  intro n L l hL
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold wP
    refine div_ne_zero ?_ (wigner_den_ne_zero L l hL)
    rw [Finset.prod_ne_zero_iff]
    intro j _
    have h1 : L j.castSucc - 1 - L l ≠ 0 := by
      have := h j.castSucc
      omega
    exact_mod_cast h1
  · unfold wM
    refine div_ne_zero ?_ (wigner_den_ne_zero L l hL)
    rw [Finset.prod_ne_zero_iff]
    intro j _
    have h1 : L j.succ + 1 - L l ≠ 0 := by
      have := h j.succ
      omega
    exact_mod_cast h1

end GlobalTheory.WigSh
