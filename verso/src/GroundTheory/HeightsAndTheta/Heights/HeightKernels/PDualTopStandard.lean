import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStdBaseChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassLinesProj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem DualTopStandard.proof (hBC : DualStdBaseChange.Statement) (hGL : GrassLinesProj.Statement) :
    DualTopStandard.Statement := by
  intro K _ _ i T _ _ b hb II hi hII
  rw [hBC K i T b hb II hi hII]
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel, hGL m II hII]

end GroundTheory.Heights₂.Heights
