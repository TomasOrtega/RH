import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCellMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular
open Module TopologicalSpace GlobalTheory.FlagPts
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagPts.continuous_cellMap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FContinuousCellMap.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.continuous_cellMap' : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), Continuous (cellMap b) := by
  first | exact @GlobalTheory.FlagPts.continuous_cellMap | exact GlobalTheory.FlagPts.continuous_cellMap | (intros; apply GlobalTheory.FlagPts.continuous_cellMap <;> assumption)
