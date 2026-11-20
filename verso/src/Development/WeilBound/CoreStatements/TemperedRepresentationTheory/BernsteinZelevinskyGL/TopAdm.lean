import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL

namespace PositivityTheory.Tls2.BZGL

/- English proof (translation)
Introduce `k _ _ _ _ n V _ _ π hπ hirr` and use `GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible k (Fin n) V π hπ hirr`.
-/
theorem irreducibleAdmissibleGL_top : GlobalTheory.Published.IrreducibleAdmissibleGL :=
  fun k _ _ _ _ n V _ _ π hπ hirr => GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible k (Fin n) V π hπ hirr

end PositivityTheory.Tls2.BZGL
