import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelClassSumsCarryChainComplexForms
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.KerJ Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FKernelClassSumsCarryChainComplexForms.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.kernelClassSums_carry_chainComplexForms : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → FormsPin t → OrbitPlaces.KFi D ex.tw := by
  first | exact @GlobalTheory.KFiClose.kFi_of_tie | exact GlobalTheory.KFiClose.kFi_of_tie | (intros; apply GlobalTheory.KFiClose.kFi_of_tie <;> assumption)
