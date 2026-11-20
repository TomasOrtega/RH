import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingPointsIdealCriterion
import Mathlib
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.factor_closedImmersion_iff_of_local` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalRingPointsIdealCriterion.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.local_ring_points_ideal_criterion : ∀ (A : Type) [CommRing A] [IsLocalRing A] (X Y : Scheme.{0}) (a : Spec (CommRingCat.of A) ⟶ X) (j : Y ⟶ X), IsClosedImmersion j → ∀ J : Ideal A, (∀ (R : Type) [CommRing R] [IsLocalRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ) → ∀ (R : Type) [CommRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ := by
  first | exact @GlobalTheory.factor_closedImmersion_iff_of_local | exact GlobalTheory.factor_closedImmersion_iff_of_local | (intros; apply GlobalTheory.factor_closedImmersion_iff_of_local <;> assumption)
