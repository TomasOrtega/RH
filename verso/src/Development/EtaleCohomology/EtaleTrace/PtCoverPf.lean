import Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfTwistCoverCocycle

open CategoryTheory AlgebraicGeometry

namespace LateralTheory.EtaleTrace

/- English proof (translation)
Introduce `k _ _ T hT`. Take `⟨Y, g, hg, y, hy⟩` from `(Scheme.geometricFiber k).jointly_surjective T hT (𝟙 (S k))`. Establish `hy' : y ≫ g = 𝟙 (S k)` using `hy`. Use `T.downward_closed hg y` as an intermediate fact. Rewrite `this` using `[hy']`. Then use the resulting hypothesis.
-/
theorem PtCover_of : PtCover := by
  intro k _ _ T hT
  obtain ⟨Y, g, hg, y, hy⟩ := (Scheme.geometricFiber k).jointly_surjective T hT (𝟙 (S k))
  have hy' : y ≫ g = 𝟙 (S k) := hy
  have := T.downward_closed hg y
  rwa [hy'] at this

end LateralTheory.EtaleTrace
