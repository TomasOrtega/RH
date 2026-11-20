import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageClosureCompleteDVRSpecialFibre
import Mathlib
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsClosedImageClosureCompleteDVRSpecialFibre.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.isClosed_image_closure_completeDVR_specialFibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y P : Scheme.{0}) (q : Y ⟶ P) (s : P ⟶ Spec (CommRingCat.of O)) (C : Set Y), IsProper s → IsImmersion q → IsProper (pullback.snd (q ≫ s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) → IsIrreducible C → (∃ y ∈ closure C, (q ≫ s) y = IsLocalRing.closedPoint O) → IsClosed (q '' closure C) := by
  first | exact @GlobalTheory.FibProperClosed.isClosed_image_closure | exact GlobalTheory.FibProperClosed.isClosed_image_closure | (intros; apply GlobalTheory.FibProperClosed.isClosed_image_closure <;> assumption)
