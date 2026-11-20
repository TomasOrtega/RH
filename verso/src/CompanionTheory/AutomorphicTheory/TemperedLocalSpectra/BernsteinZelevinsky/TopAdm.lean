import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL

namespace CompanionTheory.Tls2.BZGL

/- English proof (translation)
Introduce `k _ _ _ _ n V _ _ π hπ hirr` and use `GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible k (Fin n) V π hπ hirr`.
-/
theorem irreducibleAdmissibleGL_top : GlobalTheory.Published.IrreducibleAdmissibleGL :=
  fun k _ _ _ _ n V _ _ π hπ hirr => GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible k (Fin n) V π hπ hirr

end CompanionTheory.Tls2.BZGL
