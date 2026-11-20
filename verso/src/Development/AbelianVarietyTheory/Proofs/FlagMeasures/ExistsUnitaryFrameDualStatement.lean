import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryFrameDual
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsUnitaryFrameDual.lean&line=243#L243)
-/
theorem _root_.GlobalTheory.T.exists_unitary_frame_dual' : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (y : Fin r → V), (∀ a b, H.h (y a) (Fr.f b) = if b = a.castSucc then 1 else 0) → (∀ a b, H.h (y a) (y b) = 0) → ∃ n : V ≃ₗ[E] V, IsUnitary H n ∧ (∀ b, n (Fr.f b) = Fr.f b) ∧ (∀ a, n (Fr.es a) = y a) ∧ ∀ v ∈ H.perp (H.X Fr.f), n v - v ∈ H.X Fr.f := by
  first | exact @GlobalTheory.UnipFrame.exists_unitary_frame_dual | exact GlobalTheory.UnipFrame.exists_unitary_frame_dual | (intros; apply GlobalTheory.UnipFrame.exists_unitary_frame_dual <;> assumption)
