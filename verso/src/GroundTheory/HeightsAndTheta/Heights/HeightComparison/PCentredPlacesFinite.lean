import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightCentredPlacesFinite
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartResidue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem CentredPlacesFinite.proof : CentredPlacesFinite.Statement := by
  intro L _ _ O hft _ m _
  have hq : Algebra.FiniteType ℤ (O ⧸ m) :=
    @Algebra.FiniteType.of_surjective ℤ O (O ⧸ m) _ _ _ _ _ hft (Ideal.Quotient.mkₐ ℤ m)
      (Ideal.Quotient.mkₐ_surjective ℤ m)
  let _ : Field (O ⧸ m) := Ideal.Quotient.field m
  obtain ⟨hp, -⟩ :=
    @natCard_eq_pow_length_of_finiteType (O ⧸ m) _
      (by convert hq <;> rfl) (ringChar (O ⧸ m))
      (ringChar.charP _)
  set p := ringChar (O ⧸ m)
  have hpm : (p : O) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (O ⧸ m) p
  have hp0 : (p : L) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine (FinitePlace.hasFiniteMulSupport hp0).subset fun w hw ↦ ?_
  have hlt := (hw.2 (p : O)).mpr hpm
  have hcoe : ((p : O) : L) = (p : L) := by simp
  rw [hcoe] at hlt
  exact hlt.ne

end GroundTheory.Heights₂.Heights
