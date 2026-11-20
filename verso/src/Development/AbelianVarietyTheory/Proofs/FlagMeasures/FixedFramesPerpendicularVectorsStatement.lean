import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFramesPerpendicularVectors
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FFixedFramesPerpendicularVectors.lean&line=167#L167)
-/
theorem _root_.GlobalTheory.T.fixed_frames_perpendicular_vectors : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (φ : P →ₗ[𝓞 D.host.E] (hS D).V) (Z : GramM D), (∀ p, φ p ∈ XLam Λ (lf D F0)) → P ≤ L0X D Λ (lf D F0) → ∀ F' ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, ∃ w : Fin (D.R.rS + 1) → (D.sp.X 0).V, (∀ b, IsWcomp D P (frame F' b) (w b) ∧ w b ∈ dualInH (D.sp.X 0).hT (perpW D (L0X D Λ (lf D F0)) P)) ∧ ((Tu D u : ℕ) : D.host.E) * (D.sp.X 0).hT (∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec (Z.submatrix Fin.castSucc id) b • w b) (∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec (Z.submatrix Fin.castSucc id) b • w b) = Gmat D ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) Z := by
  first | exact @GlobalTheory.LoopC.WMem.main | exact GlobalTheory.LoopC.WMem.main | (intros; apply GlobalTheory.LoopC.WMem.main <;> assumption)
