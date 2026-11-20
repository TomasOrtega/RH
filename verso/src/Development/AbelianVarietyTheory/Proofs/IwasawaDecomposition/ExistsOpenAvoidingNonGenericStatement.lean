import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenAvoidingNonGeneric
import Mathlib
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.shrink_nbhd_generise_centre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsOpenAvoidingNonGeneric.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_open_avoiding_non_generic : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (P : X → Prop) (G : Set X), IsOpen G → ∀ (U : X.Opens) (z : X), z ∈ U → (∀ q ∈ U, P q → ∀ η : X, η ⤳ q → η ≠ q → η ∈ G) → ∃ V : X.Opens, V ≤ U ∧ z ∈ V ∧ ∀ q ∈ V, P q → q ∈ G ∨ q ⤳ z := by
  first | exact @GlobalTheory.shrink_nbhd_generise_centre | exact GlobalTheory.shrink_nbhd_generise_centre | (intros; apply GlobalTheory.shrink_nbhd_generise_centre <;> assumption)
