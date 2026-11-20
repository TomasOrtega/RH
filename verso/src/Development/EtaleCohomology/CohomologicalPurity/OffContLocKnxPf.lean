import Development.EtaleCohomology.CohomologicalPurity.EtalePurityContinuityOffClosedOfLocalAndChase

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem span_range_mul_span_singleton {A : Type} [CommRing A] {r : ℕ} (x : Fin r → A) (f : A) :
    Ideal.span (Set.range x) * Ideal.span {f} = Ideal.span (Set.range (fun k => x k * f)) := by
  rw [Ideal.span_mul_span', Set.mul_singleton, ← Set.range_comp]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem OffContLoc_of : OffContLoc := by
  intro _ r hN q A B _ _ φ x f hq J _ _ D s t hc he n i
  rw [span_range_mul_span_singleton]
  exact hN q φ (fun k => x k * f) hq J D s t hc he n i

end LateralTheory.CohomologicalPurity
