import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CBCardNC

open Finset

namespace HSDoublingWork

open Formalism.MainNotions.Ext.CutB

variable {N : ℕ} (ε : Fin N → Bool) (z : cBNC ε → ℂ)

noncomputable def U (x : Fin N × Fin N) : ℝ :=
  if h : x.1 < x.2 ∧ ε x.1 ≠ ε x.2 then ‖z ⟨x, h⟩‖ ^ 2 else 0

/- English proof (translation)
Extract witnesses or component facts from the available result. Simplify by unfolding definitions. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Simplify using the standard rewrite rules.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Evaluate the numerical expressions.
-/
theorem entry (x : Fin N × Fin N) : ‖cBpp ε z x.1 x.2‖ ^ 2 = U ε z x + U ε z x.swap := by
  obtain ⟨a, b⟩ := x
  dsimp only [cBpp, U, Prod.swap]
  by_cases h1 : a < b ∧ ε a ≠ ε b
  · have h2 : ¬ (b < a ∧ ε b ≠ ε a) := fun h => absurd h1.1 (not_lt.2 h.1.le)
    simp only [dif_pos h1, dif_neg h2, add_zero]
  · by_cases h3 : b < a ∧ ε b ≠ ε a
    · simp only [dif_neg h1, dif_pos h3, zero_add, norm_star]
    · simp only [dif_neg h1, dif_neg h3, norm_zero]
      norm_num

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sumU : ∑ x, U ε z x = ∑ pr : cBNC ε, ‖z pr‖ ^ 2 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Fin N × Fin N => x.1 < x.2 ∧ ε x.1 ≠ ε x.2) (U ε z)]
  have h0 : ∑ i : {x : Fin N × Fin N // ¬ (x.1 < x.2 ∧ ε x.1 ≠ ε x.2)}, U ε z i = 0 :=
    Finset.sum_eq_zero (fun i _ => dif_neg i.2)
  rw [h0, add_zero]
  exact Finset.sum_congr rfl (fun i _ => dif_pos i.2)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sumSwap : ∑ x : Fin N × Fin N, U ε z x.swap = ∑ x, U ε z x :=
  Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : cBhsPP := by
  intro N ε z
  unfold cBhs
  rw [← Fintype.sum_prod_type' (fun a b => ‖cBpp ε z a b‖ ^ 2)]
  rw [Finset.sum_congr rfl (fun x _ => entry ε z x), Finset.sum_add_distrib, sumSwap, sumU]
  ring

end HSDoublingWork
