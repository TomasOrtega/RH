import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem locallyQuasiFinite_of_bijective_geometric_points :
    ∀ (X T : Scheme.{0}) (f : X ⟶ T), LocallyOfFiniteType f →
      (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        ∃! x : Spec (.of Ω) ⟶ X, x ≫ f = t) → LocallyQuasiFinite f := by
  intro X T f hf h
  refine locallyQuasiFinite_of_finite_geometric_points f fun Ω _ _ t ↦ ?_
  obtain ⟨x₀, -, hx₀⟩ := h Ω t
  haveI : Subsingleton {x : Spec (.of Ω) ⟶ X // x ≫ f = t} :=
    ⟨fun a b ↦ Subtype.ext ((hx₀ a.1 a.2).trans (hx₀ b.1 b.2).symm)⟩
  infer_instance

end GlobalTheory
