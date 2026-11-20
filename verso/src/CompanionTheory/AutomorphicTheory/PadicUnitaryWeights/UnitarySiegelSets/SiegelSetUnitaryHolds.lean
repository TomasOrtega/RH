import Mathlib
import CompanionTheory.ThickeningEstimates.LieGroupReduction.SiegelPar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneStrongApproxGeneratorImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BlockTriangularMemMinimalParabolic
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary

namespace CompanionTheory.Prw

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem siegelCore_holds : CompanionTheory.ThKR.SiegelCore :=
  GlobalTheory.CompanionTheory.SiegelRed.siegelCore

end CompanionTheory.Prw
