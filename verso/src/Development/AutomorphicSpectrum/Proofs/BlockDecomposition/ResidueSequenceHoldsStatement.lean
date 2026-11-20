import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZRes.resSeq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FResidueSequenceHolds.lean&line=315#L315)
-/
theorem _root_.GlobalTheory.T.residue_sequence_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ResSeq k := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.resSeq | exact GlobalTheory.CompanionTheory.BZRes.resSeq | (intros; apply GlobalTheory.CompanionTheory.BZRes.resSeq <;> assumption)
