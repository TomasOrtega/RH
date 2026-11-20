import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanLocal
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GenGK.gkLocal_gen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGelfandKazhdanLocal.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.gelfand_kazhdan_local : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k := by
  first | exact @GlobalTheory.CompanionTheory.GenGK.gkLocal_gen | exact GlobalTheory.CompanionTheory.GenGK.gkLocal_gen | (intros; apply GlobalTheory.CompanionTheory.GenGK.gkLocal_gen <;> assumption)
