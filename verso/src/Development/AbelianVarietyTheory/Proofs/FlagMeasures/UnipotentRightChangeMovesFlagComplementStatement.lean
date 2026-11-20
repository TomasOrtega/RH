import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRightChangeMovesFlagComplement
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnipRight.unip_right` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FUnipotentRightChangeMovesFlagComplement.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.unipotent_right_change_moves_flag_complement : ∀ (D : D7) (T' : D.host.E) (F' : LFlag (VS D) D.R.rS T') (γ₁ γ₂ m n' : GV D), γ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → n' ∈ NRat F' → γ₂ = m * γ₁ * n' → ∀ x' ∈ orth (VS D) (Xsp (mapLF γ₁ F')), m x' - (γ₂ * γ₁⁻¹) x' ∈ Xsp (mapLF γ₂ F') := by
  first | exact @GlobalTheory.UnipRight.unip_right | exact GlobalTheory.UnipRight.unip_right | (intros; apply GlobalTheory.UnipRight.unip_right <;> assumption)
