import Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfTwistCoverCocycle

open CategoryTheory AlgebraicGeometry

namespace LateralTheory.EtaleTrace

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem PtCover_of : PtCover := by
  intro k _ _ T hT
  obtain ⟨Y, g, hg, y, hy⟩ := (Scheme.geometricFiber k).jointly_surjective T hT (𝟙 (S k))
  have hy' : y ≫ g = 𝟙 (S k) := hy
  have := T.downward_closed hg y
  rwa [hy'] at this

end LateralTheory.EtaleTrace
