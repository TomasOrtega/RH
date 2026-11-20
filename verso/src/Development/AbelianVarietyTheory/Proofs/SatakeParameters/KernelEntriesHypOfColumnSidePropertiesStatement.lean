import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfColumnSideProperties
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.colSide_hyp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FKernelEntriesHypOfColumnSideProperties.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.kernelEntries_hyp_of_columnSideProperties : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.KerJ.ColSide t → t.TopPinned → t.Hyp := by
  first | exact @GlobalTheory.colSide_hyp | exact GlobalTheory.colSide_hyp | (intros; apply GlobalTheory.colSide_hyp <;> assumption)
