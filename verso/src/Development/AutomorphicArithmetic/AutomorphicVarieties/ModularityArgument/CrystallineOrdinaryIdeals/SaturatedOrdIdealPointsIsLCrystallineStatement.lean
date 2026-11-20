import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatedOrdIdealPointsIsLCrystalline
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OrdLoc.ptsCr_IY` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FAutomorphicVarieties%2FModularityArgument%2FCrystallineOrdinaryIdeals%2FSaturatedOrdIdealPointsIsLCrystalline.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.saturatedOrdIdeal_points_isLCrystalline : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ), GlobalTheory.OrdLoc.PtsCr D U (GlobalTheory.OrdLoc.IY D U) := by
  first | exact @GlobalTheory.OrdLoc.ptsCr_IY | exact GlobalTheory.OrdLoc.ptsCr_IY | (intros; apply GlobalTheory.OrdLoc.ptsCr_IY <;> assumption)
