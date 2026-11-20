import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOfClosedCoverInUniversallyClose
import Mathlib
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUniversallyClosedOfClosedCoverInUniversallyClose.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.universallyClosed_of_closed_image_cover : ∀ (S X Y P : Scheme.{0}) (f : X ⟶ S) (π : Y ⟶ X) (q : Y ⟶ P) (s : P ⟶ S) (T : Set Y), UniversallyClosed s → IsImmersion q → q ≫ s = π ≫ f → IsClosed T → IsClosed (q '' T) → π '' T = Set.univ → UniversallyClosed f := by
  first | exact @GlobalTheory.universallyClosed_of_closed_cover_in_universallyClosed | exact GlobalTheory.universallyClosed_of_closed_cover_in_universallyClosed | (intros; apply GlobalTheory.universallyClosed_of_closed_cover_in_universallyClosed <;> assumption)
