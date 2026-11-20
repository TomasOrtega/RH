import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem piSeries : PiSeriesStatement := by
  intro LL ι _
  refine ⟨fun f => ?_, fun F => ⟨fun k => ?_, ?_⟩⟩
  · refine ⟨PowerSeries.mk fun n i => coeff n (f i), fun i => ?_, fun G hG => ?_⟩
    · ext n
      simp [coeff_map]
    · ext n i
      rw [coeff_mk, ← hG i, coeff_map]
      rfl
  · simp only [X_pow_dvd_iff, coeff_map]
    constructor
    · intro h i d hd
      rw [h d hd]
      rfl
    · intro h d hd
      funext i
      exact h i d hd
  · rw [isUnit_iff_constantCoeff, Pi.isUnit_iff]
    refine forall_congr' fun i => ?_
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      coeff_map]
    rfl

end LevelStatements.Lv
