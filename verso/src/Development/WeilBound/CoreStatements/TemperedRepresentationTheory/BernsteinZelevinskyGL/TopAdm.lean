import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL

namespace PositivityTheory.Tls2.BZGL

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem irreducibleAdmissibleGL_top : GlobalTheory.Published.IrreducibleAdmissibleGL :=
  fun k _ _ _ _ n V _ _ π hπ hirr => GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible k (Fin n) V π hπ hirr

end PositivityTheory.Tls2.BZGL
