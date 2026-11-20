import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRowsFixedByLabelTupleOpOfSumFixed
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LabFix.mem_VT_of_sum_fixed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMemRowsFixedByLabelTupleOpOfSumFixed.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.mem_rowsFixedByLabelTupleOp_of_sum_fixed : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf), IsRedHom X red → IsSec X red sec → ∀ (t : Tup2 D), (∀ k v, IsLabel D k (t k v)) → ∀ f ∈ HHX X, ∑ᶠ γ, serCoef t γ • X.B.R ((1, sec γ) : X.B.I.GA) f = f → f ∈ VT X t := by
  first | exact @GlobalTheory.LabFix.mem_VT_of_sum_fixed | exact GlobalTheory.LabFix.mem_VT_of_sum_fixed | (intros; apply GlobalTheory.LabFix.mem_VT_of_sum_fixed <;> assumption)
