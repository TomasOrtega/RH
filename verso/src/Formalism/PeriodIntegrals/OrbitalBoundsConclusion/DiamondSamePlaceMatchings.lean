import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.DnDiaSame0FHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.UpSame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.EqualDiagonalEntriesAll

namespace SameDiaZero

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Treat this case separately.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem diamond_same_place_matchings : Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.SameAll := by
  intro D u T
  refine ⟨?_, ?_, ?_⟩
  · apply upSame <;> assumption
  · apply dnDiaSame0F_holds <;> assumption
  · first
      | (apply eSame <;> assumption)
      | (apply e_main <;> assumption)
      | (apply eDiaSame0F <;> assumption)

end SameDiaZero
