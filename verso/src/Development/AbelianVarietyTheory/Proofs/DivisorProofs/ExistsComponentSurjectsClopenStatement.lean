import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentSurjectsClopen
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.clopen_image_irreducibleComponent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsComponentSurjectsClopen.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.exists_component_surjects_clopen : ∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : A → B), Continuous f → IsOpenMap f → IsClosedMap f →
    (∀ C ∈ irreducibleComponents A, IsOpen C) → ∀ S : Set B, IsClopen S → IsPreconnected S → ∀ a : A, f a ∈ S →
    ∃ C ∈ irreducibleComponents A, a ∈ C ∧ f '' C = S := by
  first | exact @GlobalTheory.clopen_image_irreducibleComponent | exact GlobalTheory.clopen_image_irreducibleComponent | (intros; apply GlobalTheory.clopen_image_irreducibleComponent <;> assumption)
