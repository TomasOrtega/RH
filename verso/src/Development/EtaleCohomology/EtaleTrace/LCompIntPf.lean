import Development.EtaleCohomology.EtaleTrace.LCompDecPf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.EtaleTrace

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem LCompInt_of : LCompInt := by
  intro k _ _ d X p hp hc
  have := hp.2
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  exact GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace p

end LateralTheory.EtaleTrace
