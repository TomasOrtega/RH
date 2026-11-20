import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.MeasurableSpaceFourthLift
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SmoothColumnLifts.ULiftOfAbs

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
The claim follows from `uLift_of_abs absLift`.
-/
theorem uLift : PositivityTheory.RgUd.Form.U.ULift k := uLift_of_abs absLift

end PositivityTheory.RgUd.Form.U.Lift2
