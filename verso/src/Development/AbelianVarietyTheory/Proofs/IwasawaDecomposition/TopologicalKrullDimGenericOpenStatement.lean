import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimGenericOpen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartTrdegEqRelDim
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Vert.Model.topologicalKrullDim_open_of_le_gen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTopologicalKrullDimGenericOpen.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.topologicalKrullDim_generic_open : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (M : GlobalTheory.Vert.Model O) (V : M.X.Opens), V ≤ M.gen → (V : Set M.X).Nonempty → topologicalKrullDim (V : Set M.X) = M.relDim := by
  first | exact @GlobalTheory.Vert.Model.topologicalKrullDim_open_of_le_gen | exact GlobalTheory.Vert.Model.topologicalKrullDim_open_of_le_gen | (intros; apply GlobalTheory.Vert.Model.topologicalKrullDim_open_of_le_gen <;> assumption)
