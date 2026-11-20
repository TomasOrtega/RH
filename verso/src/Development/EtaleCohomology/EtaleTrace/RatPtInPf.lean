import Development.EtaleCohomology.EtaleTrace.FibrePf
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

/- English proof (translation)
Introduce `k _ _ P r hr V hV`. Use `hr` as an intermediate fact. Establish `: JacobsonSpace P` using `LocallyOfFiniteType.jacobsonSpace r`. Take `⟨x, hxV, hxc⟩` from `nonempty_inter_closedPoints hV V.isOpen.isLocallyClosed`. Use `⟨⟨pointOfClosedPoint r x hxc, pointOfClosedPoint_comp r x hxc⟩, fun a => ?_⟩` and prove the remaining obligations.

Establish `h` using `pointOfClosedPoint_apply r x hxc a`. Use `show (pointOfClosedPoint r x hxc) a ∈ V`. Rewrite using `[h]`. Conclude with `hxV`.
-/
theorem RatPtIn_of : RatPtIn := by
  intro k _ _ P r hr V hV
  have := hr
  have : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace r
  obtain ⟨x, hxV, hxc⟩ := nonempty_inter_closedPoints hV V.isOpen.isLocallyClosed
  refine ⟨⟨pointOfClosedPoint r x hxc, pointOfClosedPoint_comp r x hxc⟩, fun a => ?_⟩
  have h := pointOfClosedPoint_apply r x hxc a
  show (pointOfClosedPoint r x hxc) a ∈ V
  rw [h]; exact hxV

end LateralTheory.EtaleTrace.Cov
