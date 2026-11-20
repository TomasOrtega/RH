import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.StepsD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VolumeSingularMatricesEqZero

open Ad3.LR

namespace GlobalTheory.CompanionTheory.GodementNull

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.Det.volume_det_fin_two_eq_zero`.
-/
theorem dNull : Ad3.LR.DNull :=
  GlobalTheory.CompanionTheory.Det.volume_det_fin_two_eq_zero

end GlobalTheory.CompanionTheory.GodementNull
