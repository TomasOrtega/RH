import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PerpendicularRankIdealBound
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FPerpendicularRankIdealBound.lean&line=215#L215)
-/
theorem _root_.GlobalTheory.T.perpendicular_rank_ideal_bound : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (s : ℕ) (Q : ℝ), s ≤ D.R.k → SubOK D (L0X D Λ (lf D F0)) P s Q → rkW D (perpW D (L0X D Λ (lf D F0)) P) = s ∧ ∃ I : Ideal (𝓞 D.host.E), I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Q ^ 2 * NT D u ^ 2 ∧ I • dualInH (D.sp.X 0).hT (perpW D (L0X D Λ (lf D F0)) P) ≤ perpW D (L0X D Λ (lf D F0)) P := by
  first | exact @GlobalTheory.LoopC.PerpDisc.main | exact GlobalTheory.LoopC.PerpDisc.main | (intros; apply GlobalTheory.LoopC.PerpDisc.main <;> assumption)
