import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetUnipotentOnBesselModels
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FStrictFundamentalSetUnipotentOnBesselModels.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.strictFundamentalSet_unipotent_on_besselModels : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1),
    GlobalTheory.DegVol.IsFund (trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u)
      (GlobalTheory.DegVol.RP D.R.k D.R.rS (fun _ => 1)) (trI C '' Y.FN u) := by
  first | exact @GlobalTheory.TypeAsm.CovTrans.isFund_trI | exact GlobalTheory.TypeAsm.CovTrans.isFund_trI | (intros; apply GlobalTheory.TypeAsm.CovTrans.isFund_trI <;> assumption)
