import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardWeightSetGridEqGridRowSpaceRank
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Grid.card_weightX_grid` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FCardWeightSetGridEqGridRowSpaceRank.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.card_weightSet_grid_eq_gridRowSpaceRank : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ((GlobalTheory.Grid.grid D τ).weightX j).card = GlobalTheory.Grid.rkX D j := by
  first | exact @GlobalTheory.Grid.card_weightX_grid | exact GlobalTheory.Grid.card_weightX_grid | (intros; apply GlobalTheory.Grid.card_weightX_grid <;> assumption)
