import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RanksFramesClosed
import Formalism.LocalToGlobal.ThresholdSelection
import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
open Formalism.BasicNotions Formalism.MainNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRanksFramesClosed.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.ranks_frames_closed : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), Formalism.L2.TSel 𝒞 → (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧ Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  first | exact @GlobalTheory.ranks_and_frame_of_tied_class | exact GlobalTheory.ranks_and_frame_of_tied_class | (intros; apply GlobalTheory.ranks_and_frame_of_tied_class <;> assumption)
