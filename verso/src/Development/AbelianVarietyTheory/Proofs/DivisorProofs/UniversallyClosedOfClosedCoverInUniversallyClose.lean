import Mathlib
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

/- English proof (translation)
Introduce `S X Y P f π q s T hs hq hcomm hT hqT hπT`. Set `I` to `Scheme.IdealSheafData.vanishingIdeal (⟨T, hT⟩ : TopologicalSpace.Closeds Y)`. Establish `hrange : Set.range I.subschemeι = T`. Rewrite using `[Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]`. Both sides reduce to the same expression.

Establish `hcl : IsClosedImmersion (I.subschemeι ≫ q)`. Use `.of_isPreimmersion _ ?_` and prove the remaining obligations. Establish `: Set.range (I.subschemeι ≫ q) = q '' T`. Rewrite using `[← hrange, ← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `hqT`. Establish `: UniversallyClosed ((I.subschemeι ≫ π) ≫ f)`. Rewrite using `[Category.assoc, ← hcomm, ← Category.assoc]`. Use `infer_instance`.

Establish `: Surjective (I.subschemeι ≫ π)`. Prove the components needed by the constructor for the conclusion. Establish `: Set.range (I.subschemeι ≫ π) = π '' T`. Rewrite using `[← hrange, ← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite using `[← Set.range_eq_univ, this]`. Conclude with `hπT`. Conclude with `UniversallyClosed.of_comp_surjective (I.subschemeι ≫ π) f`.
-/
theorem universallyClosed_of_closed_cover_in_universallyClosed :
    ∀ (S X Y P : Scheme.{0}) (f : X ⟶ S) (π : Y ⟶ X) (q : Y ⟶ P) (s : P ⟶ S) (T : Set Y),
      UniversallyClosed s → IsImmersion q → q ≫ s = π ≫ f → IsClosed T → IsClosed (q '' T) →
        π '' T = Set.univ → UniversallyClosed f := by
  intro S X Y P f π q s T hs hq hcomm hT hqT hπT
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨T, hT⟩ : TopologicalSpace.Closeds Y)
  have hrange : Set.range I.subschemeι = T := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hcl : IsClosedImmersion (I.subschemeι ≫ q) := by
    refine .of_isPreimmersion _ ?_
    have : Set.range (I.subschemeι ≫ q) = q '' T := by
      rw [← hrange, ← Set.range_comp]; rfl
    rw [this]; exact hqT
  have : UniversallyClosed ((I.subschemeι ≫ π) ≫ f) := by
    rw [Category.assoc, ← hcomm, ← Category.assoc]
    infer_instance
  have : Surjective (I.subschemeι ≫ π) := by
    constructor
    have : Set.range (I.subschemeι ≫ π) = π '' T := by
      rw [← hrange, ← Set.range_comp]; rfl
    rw [← Set.range_eq_univ, this]; exact hπT
  exact UniversallyClosed.of_comp_surjective (I.subschemeι ≫ π) f

end GlobalTheory
