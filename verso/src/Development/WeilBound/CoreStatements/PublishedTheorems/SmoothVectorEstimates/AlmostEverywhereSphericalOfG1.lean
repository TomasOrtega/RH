import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalAlmostEverywhereOfBounded

namespace PositivityTheory.jumpWindows

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.StrongMultOne.spherical_almost_everywhere_of_bounded`.
-/
theorem almost_everywhere_spherical_of_G1 : G1 → AlmostEverywhereSpherical :=
  GlobalTheory.CompanionTheory.StrongMultOne.spherical_almost_everywhere_of_bounded

end PositivityTheory.jumpWindows
