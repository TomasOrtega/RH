import Mathlib
import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne
import Formalism.FormalGroupWitt.WeightInvariance
import Formalism.TorsionNormIteration.LubinTateExample

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Normalize the expressions using the abelian group laws. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem norm_for_all_alpha : NormAllAlpha := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm tr hinj hnm htr hadd hlin hadj h2 α α' u hu2 hα hα'
  have symm : ∀ a b, cob φ a b = cob φ b a := by
    intro a b; unfold cob; rw [add_comm a b]; abel
  have add2 : ∀ a b b', cob φ a (b + b') = cob φ a b + cob φ a b' := by
    intro a b b'; rw [symm, hadd, symm b, symm b']
  have e1 : φ ((α + α') • u) = φ (α • u) + φ (α' • u) + cob φ (α • u) (α' • u) := by
    unfold cob; rw [add_smul]; abel
  have e2 : cob φ (α • u) (α' • u) = cob φ u ((star α * α') • u) := by rw [hadj, smul_smul]
  have e3 : cob φ u ((star α * α') • u) + cob φ u ((star α * α') • u)
      = (tr (star α * α')) • cob φ u u := by
    have h : cob φ u ((star α * α') • u) = cob φ u (star (star α * α') • u) := by
      rw [symm, hadj]
    nth_rewrite 1 [h]; rw [← add2, ← add_smul, ← htr, hlin]
  have e4 : cob φ u u = φ u + φ u := by
    unfold cob; rw [← two_smul O u, hu2]
    have : (4 : Z) • φ u = φ u + φ u + φ u + φ u := by
      rw [show (4 : Z) = 1 + 1 + 1 + 1 by norm_num]; simp [add_smul]
    rw [this]; abel
  have e5 : cob φ u ((star α * α') • u) = tr (star α * α') • φ u := by
    apply sub_eq_zero.1; apply h2
    have : ∀ x y : Q, (x - y) + (x - y) = (x + x) - (y + y) := by intro x y; abel
    rw [this, e3, e4, smul_add, sub_self]
  have e6 : nm (α + α') = nm α + nm α' + tr (star α * α') := by
    apply hinj; simp only [map_add, hnm, htr, star_add, star_mul, star_star]; ring
  rw [e1, e2, e5, hα, hα', e6, add_smul, add_smul]

end Formalism.HermitianLattices.IntegralLatticeDensity
