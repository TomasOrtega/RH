import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsExactGramFrameInTermClass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LoopC.FrameMove.exists_exact_frame` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsExactGramFrameInTermClass.lean&line=450#L450)
-/
theorem _root_.GlobalTheory.T.exists_exactGram_frame_in_termClass : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (Z : GramM D), ∀ F' ∈ FrSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P, ∃ F'' ∈ ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P, TEqv D Λ (lf D F0) F' F'' := by
  first | exact @GlobalTheory.LoopC.FrameMove.exists_exact_frame | exact GlobalTheory.LoopC.FrameMove.exists_exact_frame | (intros; apply GlobalTheory.LoopC.FrameMove.exists_exact_frame <;> assumption)
