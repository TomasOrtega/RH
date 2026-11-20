import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

/- English proof (translation)
Use extensionality with `m`. Simplify using the standard rewrite rules.
-/
theorem MertensUpper.Iic_eq_range (n : ℕ) : Finset.Iic n = Finset.range (n + 1) := by
  ext m
  simp

/- English proof (translation)
Unfold `GroundTheory.Heights₂.Heights.Model.MertensUpper.Statement GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.MertensUpper.Statement`. Simplify using `only [MertensUpper.Iic_eq_range]`.
-/
theorem MertensUpper.equiv :
    GroundTheory.Heights₂.Heights.Model.MertensUpper.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.MertensUpper.Statement := by
  unfold GroundTheory.Heights₂.Heights.Model.MertensUpper.Statement
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.MertensUpper.Statement
  simp only [MertensUpper.Iic_eq_range]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
