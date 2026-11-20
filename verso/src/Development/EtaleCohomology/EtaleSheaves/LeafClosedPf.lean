import Development.EtaleCohomology.EtaleSheaves.LeafGeoCut

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.LeafClosedPf

/- English proof (translation)
Introduce `B V`. Set `Z : TopologicalSpace.Closeds B` to `⟨(V : Set B)ᶜ, V.isOpen.isClosed_compl⟩`. Set `I` to `Scheme.IdealSheafData.vanishingIdeal Z`. Use `⟨I.subscheme, I.subschemeι, inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]`.

Simplify using `[Z]`.
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
