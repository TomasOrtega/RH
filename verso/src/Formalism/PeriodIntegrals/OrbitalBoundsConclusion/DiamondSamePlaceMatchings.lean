import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.DnDiaSame0FHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.UpSame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.EqualDiagonalEntriesAll

namespace SameDiaZero

/- English proof (translation)
Introduce `D u T`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `apply upSame <;> assumption`. Apply the tactic sequence `apply dnDiaSame0F_holds <;> assumption`. Use `first`.

Consider the case `(apply eSame <;> assumption)`. Consider the case `(apply e_main <;> assumption)`. Consider the case `(apply eDiaSame0F <;> assumption)`.
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
