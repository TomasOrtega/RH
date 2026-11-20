import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesCoverExists

namespace PositivityTheory.RgFd.B

open PositivityTheory.RgDs

/- English proof (translation)
The claim follows from `fdAll_of_key K.key_identity_holds Hilb.hilbert_space_realisation_holds`.
-/
theorem fdAll : FdAll := fdAll_of_key K.key_identity_holds Hilb.hilbert_space_realisation_holds

/- English proof (translation)
The claim follows from `realMetaplectic_of_forall fdAll`.
-/
theorem formalDegreeCompactDual : GlobalTheory.Published.FormalDegreeCompactDual := realMetaplectic_of_forall fdAll

end PositivityTheory.RgFd.B
