import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitriangularFramesGramEqCellPoint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsUnitriangularFramesGramEqCellPoint.lean&line=101#L101)
-/
theorem _root_.GlobalTheory.T.exists_unitriangular_frames_gram_eq_cell_point : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F₁ : LFlag (VS D) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → IsInCell (ZhatOM (ZhatL F F₁)) w → (∃ (F00 : LFlag (VS D) D.R.rS T) (F'0 : LFlag (VS D) D.R.rS T'), Tri D.host.E (frame F) (frame F00) ∧ Tri D.host.E (frame F₁) (frame F'0) ∧ ZhatOM (ZhatL F00 F'0) = ptMat w) ∧ ∀ (F₂ : LFlag (VS D) D.R.rS T) (F₃ : LFlag (VS D) D.R.rS T'), Tri D.host.E (frame F) (frame F₂) → Tri D.host.E (frame F₁) (frame F₃) → IsInCell (ZhatOM (ZhatL F₂ F₃)) w ∧ Gval F₂ F₃ = Gval F F₁ := by
  first | exact @GlobalTheory.LocOver.base_frames_at_point | exact GlobalTheory.LocOver.base_frames_at_point | (intros; apply GlobalTheory.LocOver.base_frames_at_point <;> assumption)
