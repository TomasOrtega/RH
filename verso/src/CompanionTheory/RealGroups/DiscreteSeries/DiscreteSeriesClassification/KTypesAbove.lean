import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.CoverExistsOf
import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.ExplicitFunctionSquareIntegrable
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.EquivariantSections.KeyIdentityHolds
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.HilbertSpaceRealisationHolds
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InfinitesimalCharacters.DiscreteSeriesInfinitesimalCharacter

namespace CompanionTheory.RgDs.B

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dsExists : GlobalTheory.Dec.DSExists := dsExists_of CompanionTheory.RgFd.explicit_function_square_integrable K.key_identity_holds Hilb.hilbert_space_realisation_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kTypesAbove : GlobalTheory.Dec.KTypesAbove := kTypesAbove_of CompanionTheory.RgFd.explicit_function_square_integrable K.key_identity_holds Hilb.hilbert_space_realisation_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dsInfChar : GlobalTheory.Dec.DSInfChar := CompanionTheory.RgDsInf.dsInfChar'

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem discreteSeriesUpqExists : GlobalTheory.Published.DiscreteSeriesUpqExists := upqExists_of dsExists

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem discreteSeriesExists : GlobalTheory.Published.DiscreteSeriesExists := exists_of dsExists

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem discreteSeriesCoverExists : GlobalTheory.Published.DiscreteSeriesCoverExists := coverExists_of dsExists

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem classUsed : ClassUsed := classUsed_of dsExists kTypesAbove dsInfChar

end CompanionTheory.RgDs.B
