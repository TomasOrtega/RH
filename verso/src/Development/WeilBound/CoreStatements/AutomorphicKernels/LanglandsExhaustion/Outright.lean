import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.EssSquareIntegrableSegmentsOfSeg
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation

namespace PositivityTheory.Exh

/- English proof (translation)
The claim follows from `standardCosocleGL_of_seg PositivityTheory.RgGu.segmentRepresentation`.
-/
theorem standardCosocleGL_holds : GlobalTheory.Published.StandardCosocleGL := standardCosocleGL_of_seg PositivityTheory.RgGu.segmentRepresentation

/- English proof (translation)
The claim follows from `langlandsExhaustionGL_of_seg PositivityTheory.RgGu.segmentRepresentation`.
-/
theorem langlandsExhaustionGL_holds : GlobalTheory.Published.LanglandsExhaustionGL := langlandsExhaustionGL_of_seg PositivityTheory.RgGu.segmentRepresentation

/- English proof (translation)
The claim follows from `langlandsMultisegments_of_seg PositivityTheory.RgGu.segmentRepresentation`.
-/
theorem langlandsMultisegments_holds : GlobalTheory.Published.LanglandsMultisegments := langlandsMultisegments_of_seg PositivityTheory.RgGu.segmentRepresentation

end PositivityTheory.Exh
