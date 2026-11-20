import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualCountBound.DualCount

noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem lattice_membership_ring : InR := by
  intro F _ _ _ E _ _ _ _ M hOK y
  unfold Model.R
  cases h : M.split with
  | none =>
    exact (M.L.O_def _).2 (isIntegral_algebraMap (x := y))
  | some g =>
    rw [Subring.mem_comap]
    refine ⟨(y, y), RingHom.mem_eqLocus.2 rfl, ?_⟩
    change ((y : F), (y : F)) = g.e (algebraMap F E (y : F))
    rw [g.e.commutes]
    rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lattice_index_modulus_le : ModLe := by
  intro F _ _ _ E _ _ _ _ M hOK x hx
  unfold Model.modK
  have hsub : (fun y => x * y) '' (M.R : Set E) ⊆ (M.R : Set E) := by
    rintro _ ⟨y, hy, rfl⟩
    exact M.R.mul_mem hx hy
  have h1 : M.mu ((fun y => x * y) '' (M.R : Set E)) ≤ 1 := by
    rw [← hOK.haar.volR]; exact MeasureTheory.measure_mono hsub
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1)

end PI.NGStepBBW
