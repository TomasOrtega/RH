import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange

namespace GlobalTheory.ThLoc

/- English proof (translation)
Introduce `p _ lam` and use `GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p lam`.
-/
theorem place_extends_to_iso : Formalism.L2.KerInert.LamExt :=
  fun p _ lam => GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p lam

end GlobalTheory.ThLoc
