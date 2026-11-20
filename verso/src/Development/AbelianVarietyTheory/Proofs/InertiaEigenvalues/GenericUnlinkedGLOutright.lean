import Mathlib
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo

namespace GlobalTheory

/- English proof (translation)
The claim follows from `GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds`.
-/
theorem genericUnlinkedGL_outright : GlobalTheory.Published.GenericUnlinkedGL :=
  GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds

end GlobalTheory
