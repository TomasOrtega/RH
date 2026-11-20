import Development.EtaleCohomology.EtaleSheaves.LeafReducedSmooth
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.ReducedOfSmooth

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem LeafReducedSmooth_of : LateralTheory.E.QuasiFiniteDescent.LeafReducedSmooth := by
  intro k _ Ω _ _ R _ D q hq
  have : Smooth q := hq.smooth
  have : _root_.IsReduced R := isReduced_of_injective R.val Subtype.val_injective
  have : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of R)) := inferInstance
  exact GlobalTheory.isReduced_of_smooth_of_isReduced q

end LateralTheory.E.ReducedOfSmooth
