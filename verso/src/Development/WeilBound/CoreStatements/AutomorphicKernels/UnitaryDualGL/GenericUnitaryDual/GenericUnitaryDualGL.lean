import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGLHolds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnitaryDualGlStatement

namespace PositivityTheory.Gud

/- English proof (translation)
Introduce `_ _ _ _ _` and use `Fin.genericUnitaryDualGL_holds`.
-/
theorem generic_unitary_dual_GL : True → GlobalTheory.Published.SquareIntegrableSegment → GlobalTheory.Published.GenericUnlinkedGL → GlobalTheory.Published.LanglandsMultisegments →
    GlobalTheory.Published.StandardCosocleGL → GlobalTheory.Published.GenericUnitaryDualGL := fun _ _ _ _ _ => Fin.genericUnitaryDualGL_holds

end PositivityTheory.Gud
