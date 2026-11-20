import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAlgebraicallyClosedPoint
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLiftAlgebraicallyClosedPoint.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_lift_algebraically_closed_point : ∀ {X Y : AlgebraicGeometry.Scheme.{0}} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f] (k : Type) [Field k] [IsAlgClosed k]
    (y : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ Y), Set.range y ⊆ Set.range f →
    ∃ x : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ X, x ≫ f = y := by
  first | exact @GlobalTheory.exists_lift_of_range_subset_of_isAlgClosed | exact GlobalTheory.exists_lift_of_range_subset_of_isAlgClosed | (intros; apply GlobalTheory.exists_lift_of_range_subset_of_isAlgClosed <;> assumption)
