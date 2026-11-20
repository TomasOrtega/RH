import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyQuasiFiniteOfUniqueGeomPoints
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.locallyQuasiFinite_of_bijective_geometric_points` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocallyQuasiFiniteOfUniqueGeomPoints.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.locallyQuasiFinite_of_unique_geom_points : ∀ (X T : Scheme.{0}) (f : X ⟶ T), LocallyOfFiniteType f → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T), ∃! x : Spec (.of Ω) ⟶ X, x ≫ f = t) → LocallyQuasiFinite f := by
  first | exact @GlobalTheory.locallyQuasiFinite_of_bijective_geometric_points | exact GlobalTheory.locallyQuasiFinite_of_bijective_geometric_points | (intros; apply GlobalTheory.locallyQuasiFinite_of_bijective_geometric_points <;> assumption)
