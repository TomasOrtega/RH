import Mathlib
import CompanionTheory.ThickeningEstimates.LieGroupReduction.SiegelPar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneStrongApproxGeneratorImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BlockTriangularMemMinimalParabolic
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary

namespace CompanionTheory.Prw

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.SiegelRed.siegelCore`.
-/
theorem siegelCore_holds : CompanionTheory.ThKR.SiegelCore :=
  GlobalTheory.CompanionTheory.SiegelRed.siegelCore

end CompanionTheory.Prw
