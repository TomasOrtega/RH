import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsContinuousCircleCharExtension
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_continuous_circle_char_extension` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FExistsContinuousCircleCharExtension.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.exists_continuous_circle_char_extension' : ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (H N : Subgroup G) (ψ : H →* Circle), IsOpen (H : Set G) → Continuous ψ → (∀ x : H, (x : G) ∈ N → ψ x = 1) → ∃ χ : G →* Circle, Continuous χ ∧ (∀ x ∈ N, χ x = 1) ∧ ∀ x : H, χ x = ψ x := by
  first | exact @GlobalTheory.exists_continuous_circle_char_extension | exact GlobalTheory.exists_continuous_circle_char_extension | (intros; apply GlobalTheory.exists_continuous_circle_char_extension <;> assumption)
