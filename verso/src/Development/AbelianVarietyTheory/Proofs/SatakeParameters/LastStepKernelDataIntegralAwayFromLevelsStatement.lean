import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepKernelDataIntegralAwayFromLevels
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TopInt.topInt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLastStepKernelDataIntegralAwayFromLevels.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.lastStepKernelData_integral_awayFromLevels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt := by
  first | exact @GlobalTheory.TopInt.topInt | exact GlobalTheory.TopInt.topInt | (intros; apply GlobalTheory.TopInt.topInt <;> assumption)
