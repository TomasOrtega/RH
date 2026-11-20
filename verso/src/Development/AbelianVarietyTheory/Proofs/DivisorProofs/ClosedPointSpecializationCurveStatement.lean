import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointSpecializationCurve
import Mathlib
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FClosedPointSpecializationCurve.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.closed_point_specialization_curve : ∀ (κ : Type) [Field κ] (V : Scheme.{0}) [IsIntegral V] (q : V ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType q]
    (x : V) (U : V.Opens), IsClosed ({x} : Set V) → (∃ v, v ∈ U) → x ∉ U →
    ∃ y : V, y ∈ U ∧ y ⤳ x ∧ topologicalKrullDim (closure ({y} : Set V)) = 1 := by
  first | exact @GlobalTheory.CurveThrough.exists_curve_through_closedPoint | exact GlobalTheory.CurveThrough.exists_curve_through_closedPoint | (intros; apply GlobalTheory.CurveThrough.exists_curve_through_closedPoint <;> assumption)
