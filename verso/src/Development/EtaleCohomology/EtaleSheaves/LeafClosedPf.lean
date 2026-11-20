import Development.EtaleCohomology.EtaleSheaves.LeafGeoCut

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.LeafClosedPf

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem LeafClosed_of : LateralTheory.E.LeafGeoCut.LeafClosed := by
  intro B V
  let Z : TopologicalSpace.Closeds B := ⟨(V : Set B)ᶜ, V.isOpen.isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  refine ⟨I.subscheme, I.subschemeι, inferInstance, ?_⟩
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  simp [Z]

end LateralTheory.E.LeafClosedPf

end
