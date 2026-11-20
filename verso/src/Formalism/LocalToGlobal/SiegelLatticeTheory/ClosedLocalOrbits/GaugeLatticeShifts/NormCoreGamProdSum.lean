import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCore

open Finset

noncomputable section

open Classical

open Formalism.L2.SG.GGMirabolic in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem Formalism.L2.SG.NormCut.gamma_product_sum_holds : Formalism.L2.SG.NormCut.GamProdSum := by
  intro ι _ Fq _ _ k ψ x
  refine ⟨?_, ?_⟩
  · unfold gamProd gam
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    congr 1
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rfl
  · rw [Nat.card_congr (Equiv.subtypePiEquivPi), Nat.card_pi]
    rfl
