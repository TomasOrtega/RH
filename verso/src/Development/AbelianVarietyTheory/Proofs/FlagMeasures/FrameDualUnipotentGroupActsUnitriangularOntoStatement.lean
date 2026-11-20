import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocOver.UnipOnto.unipotent_onto` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FFrameDualUnipotentGroupActsUnitriangularOnto.lean&line=469#L469)
-/
theorem _root_.GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ Fr : FrameD H r, Fr.T ≠ 0 → (∀ n, n ∈ Fr.N ↔ n ∈ NU H Fr.f) ∧ (∀ n ∈ Fr.N, Tri E Fr.f fun b => n (Fr.f b)) ∧ ∀ g : Fin (r + 1) → V, Tri E Fr.f g → ∃ n ∈ Fr.N, g = fun b => n (Fr.f b) := by
  first | exact @GlobalTheory.LocOver.UnipOnto.unipotent_onto | exact GlobalTheory.LocOver.UnipOnto.unipotent_onto | (intros; apply GlobalTheory.LocOver.UnipOnto.unipotent_onto <;> assumption)
