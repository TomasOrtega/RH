import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.CoverExistsOf
import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.ExplicitFunctionSquareIntegrable
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.EquivariantSections.KeyIdentityHolds
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.HilbertSpaceRealisationHolds
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InfinitesimalCharacters.DiscreteSeriesInfinitesimalCharacter

namespace CompanionTheory.RgDs.B

/- English proof (translation)
The claim follows from `dsExists_of CompanionTheory.RgFd.explicit_function_square_integrable K.key_identity_holds Hilb.hilbert_space_realisation_holds`.
-/
theorem dsExists : GlobalTheory.Dec.DSExists := dsExists_of CompanionTheory.RgFd.explicit_function_square_integrable K.key_identity_holds Hilb.hilbert_space_realisation_holds

/- English proof (translation)
The claim follows from `kTypesAbove_of CompanionTheory.RgFd.explicit_function_square_integrable K.key_identity_holds Hilb.hilbert_space_realisation_holds`.
-/
theorem kTypesAbove : GlobalTheory.Dec.KTypesAbove := kTypesAbove_of CompanionTheory.RgFd.explicit_function_square_integrable K.key_identity_holds Hilb.hilbert_space_realisation_holds

/- English proof (translation)
The claim follows from `CompanionTheory.RgDsInf.dsInfChar'`.
-/
theorem dsInfChar : GlobalTheory.Dec.DSInfChar := CompanionTheory.RgDsInf.dsInfChar'

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

/- English proof (translation)
The claim follows from `classUsed_of dsExists kTypesAbove dsInfChar`.
-/
theorem classUsed : ClassUsed := classUsed_of dsExists kTypesAbove dsInfChar

end CompanionTheory.RgDs.B
