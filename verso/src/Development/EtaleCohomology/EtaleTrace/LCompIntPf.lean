import Development.EtaleCohomology.EtaleTrace.LCompDecPf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.EtaleTrace

/- English proof (translation)
Introduce `k _ _ d X p hp hc`. Use `hp.2` as an intermediate fact. Establish `: Smooth p` using `SmoothOfRelativeDimension.smooth d p`. Conclude with `GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace p`.
-/
theorem LCompInt_of : LCompInt := by
  intro k _ _ d X p hp hc
  have := hp.2
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  exact GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace p

end LateralTheory.EtaleTrace
