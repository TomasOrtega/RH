import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardIntegralFramesFixedLiftLe
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCardIntegralFramesFixedLiftLe.lean&line=412#L412)
-/
theorem _root_.GlobalTheory.T.card_integral_frames_fixed_lift_le : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (φ : P →ₗ[𝓞 D.host.E] (hS D).V) (Z : GramM D) (s : ℕ) (De Q : ℝ), 1 ≤ s → s ≤ D.R.k → (∀ p, φ p ∈ XLam Λ (lf D F0)) → SubOK D (L0X D Λ (lf D F0)) P s De → QOK D u u' Z Q → (cntCl (FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤ ENNReal.ofReal (fixB D s (NT D u) De Q) := by
  first | exact @GlobalTheory.LoopC.FixedLift.card_frames_le | exact GlobalTheory.LoopC.FixedLift.card_frames_le | (intros; apply GlobalTheory.LoopC.FixedLift.card_frames_le <;> assumption)
