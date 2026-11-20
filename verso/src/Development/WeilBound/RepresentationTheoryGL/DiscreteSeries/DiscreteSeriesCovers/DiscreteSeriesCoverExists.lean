import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.CoverExistsOf
import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.ExplicitFunctionSquareIntegrable
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.KeyIdentityHolds
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.HilbertSpaceRealisationHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementsActByGelfandValues
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitActGlRel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapQdetEtr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EwordCoef
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumCycWordEqEtr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFinSmoothBoth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsDSSkImpUpqRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefSmoothOnG

namespace PositivityTheory.RgDs.B

/- English proof (translation)
The claim follows from `dsExists_of PositivityTheory.RgFd.explicit_function_square_integrable K.key_identity_holds Hilb.hilbert_space_realisation_holds`.
-/
theorem dsExists : GlobalTheory.Dec.DSExists := dsExists_of PositivityTheory.RgFd.explicit_function_square_integrable K.key_identity_holds Hilb.hilbert_space_realisation_holds

/- English proof (translation)
The claim follows from `upqExists_of dsExists`.
-/
theorem discreteSeriesUpqExists : GlobalTheory.Published.DiscreteSeriesUpqExists := upqExists_of dsExists

/- English proof (translation)
The claim follows from `exists_of dsExists`.
-/
theorem discreteSeriesExists : GlobalTheory.Published.DiscreteSeriesExists := exists_of dsExists

/- English proof (translation)
The claim follows from `coverExists_of dsExists`.
-/
theorem discreteSeriesCoverExists : GlobalTheory.Published.DiscreteSeriesCoverExists := coverExists_of dsExists

end PositivityTheory.RgDs.B
