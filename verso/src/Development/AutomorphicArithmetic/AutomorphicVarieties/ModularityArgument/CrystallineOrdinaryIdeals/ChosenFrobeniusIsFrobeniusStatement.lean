import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ChosenFrobeniusIsFrobenius
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OrdLoc.fr_isFr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FAutomorphicVarieties%2FModularityArgument%2FCrystallineOrdinaryIdeals%2FChosenFrobeniusIsFrobenius.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.chosenFrobenius_isFrobenius : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O), GlobalTheory.OrdLoc.IsFr D (GlobalTheory.OrdLoc.fr D) := by
  first | exact @GlobalTheory.OrdLoc.fr_isFr | exact GlobalTheory.OrdLoc.fr_isFr | (intros; apply GlobalTheory.OrdLoc.fr_isFr <;> assumption)
