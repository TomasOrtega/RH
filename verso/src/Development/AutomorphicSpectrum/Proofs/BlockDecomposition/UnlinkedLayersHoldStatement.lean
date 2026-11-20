import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedLayersHold
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnlinkedLayersHold.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.unlinked_layers_hold : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], UnlinkedLayers k := by
  first | exact @GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers | exact GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers | (intros; apply GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers <;> assumption)
