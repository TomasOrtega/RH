import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelExpansionAbsoluteConvergenceEqualWords
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCLC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Core.Diag.kExp_absConv_tied` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FKernelExpansionAbsoluteConvergenceEqualWords.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.kernel_expansion_absolute_convergence_equal_words : Formalism.L2.SG.ThmSOwn.KExpTied ∧ AbsConvTied := by
  first | exact @GlobalTheory.Core.Diag.kExp_absConv_tied | exact GlobalTheory.Core.Diag.kExp_absConv_tied | (intros; apply GlobalTheory.Core.Diag.kExp_absConv_tied <;> assumption)
