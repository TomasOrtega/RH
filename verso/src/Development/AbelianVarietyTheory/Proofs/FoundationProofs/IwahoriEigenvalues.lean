import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvaluesOfNewton

namespace GlobalTheory.IwahoriEigenObj

/- English proof (translation)
The claim follows from `GlobalTheory.IwahoriEigen.iwahoriEigenvalues`.
-/
theorem iwahoriEigenvalues : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues :=
  GlobalTheory.IwahoriEigen.iwahoriEigenvalues

end GlobalTheory.IwahoriEigenObj
