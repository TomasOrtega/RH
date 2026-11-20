import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermNormsGeOneAndBounded
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelevantSetZeroGNotIdentity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStarStableIdealAbsorbingMinors
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRelevantTermNormsGeOneAndBounded.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.relevantTerm_norms_ge_one_and_bounded : ∀ (Cg cb Cw cT CT C0 CH C' Cl : ℝ), 0 ≤ CH → ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X)
    (u : D.what₂.Word), HostC → NFExC → LabC → TermC → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 →
    ∀ t ∈ relSet Y u, 1 ≤ k2Del D (jT t) (labT t) ∧ 1 ≤ DbL D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 ∧
      DbL D (jT t) (labT t) ≤ (Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2) ^ D.R.rS := by
  first | exact @GlobalTheory.TypeAsm.PairsLab.norms_of_relevant | exact GlobalTheory.TypeAsm.PairsLab.norms_of_relevant | (intros; apply GlobalTheory.TypeAsm.PairsLab.norms_of_relevant <;> assumption)
