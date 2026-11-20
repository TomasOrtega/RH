import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual

namespace GlobalTheory

/- English proof (translation)
The claim follows from `GlobalTheory.DualLat.dualFr_lattice_and_hdual.1`.
-/
theorem dualFrLattice_holds : Formalism.L2.DIV.DualFrLattice :=
  GlobalTheory.DualLat.dualFr_lattice_and_hdual.1

end GlobalTheory
