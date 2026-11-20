import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NullSingOfIdemEx

namespace PositivityTheory.Rg.Rsw.L

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.NullFr.nullSing_of_idemEx`.
-/
theorem nullSing : IdemEx → NullSing := GlobalTheory.CompanionTheory.NullFr.nullSing_of_idemEx

end PositivityTheory.Rg.Rsw.L
