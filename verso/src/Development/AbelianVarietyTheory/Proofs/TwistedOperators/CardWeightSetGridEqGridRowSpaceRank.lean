import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMinimalGapEqChiGridGapGammaOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.Grid

/- English proof (translation)
Introduce `D _ τ j _ hj`. Establish `hcen : GlobalTheory.Grid.cen D τ = GlobalTheory.ChiGrid.cen D 1 τ`. Use function extensionality and compare the values at `i`. Unfold `GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf`. Rewrite using `[GlobalTheory.GridJoin.gap_eq_chiGap D]`.

Both sides reduce to the same expression. Establish `hg : GlobalTheory.Grid.grid D τ = GlobalTheory.ChiGrid.num D 1 τ`. Unfold `GlobalTheory.Grid.grid GlobalTheory.Grid.gridOf GlobalTheory.ChiGrid.num`. Rewrite using `[hcen, GlobalTheory.GridJoin.gap_eq_chiGap D]`. Both sides reduce to the same expression.

Rewrite using `[hg, GlobalTheory.FunObj.card_weightX D 1 τ hj]`. Both sides reduce to the same expression.
-/
theorem card_weightX_grid : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (j : ℕ), 1 ≤ j → j ≤ D.R.m →
    ((GlobalTheory.Grid.grid D τ).weightX j).card = GlobalTheory.Grid.rkX D j := by
  intro D _ τ j _ hj
  have hcen : GlobalTheory.Grid.cen D τ = GlobalTheory.ChiGrid.cen D 1 τ := by
    funext i
    unfold GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf
    rw [GlobalTheory.GridJoin.gap_eq_chiGap D]
    rfl
  have hg : GlobalTheory.Grid.grid D τ = GlobalTheory.ChiGrid.num D 1 τ := by
    unfold GlobalTheory.Grid.grid GlobalTheory.Grid.gridOf GlobalTheory.ChiGrid.num
    rw [hcen, GlobalTheory.GridJoin.gap_eq_chiGap D]
    rfl
  rw [hg, GlobalTheory.FunObj.card_weightX D 1 τ hj]
  rfl

end GlobalTheory.Grid
