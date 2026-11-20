import Development.EtaleCohomology.EtaleSheaves.PartDiagCut

namespace LateralTheory.E.DiagNatPf
open LateralTheory.E.PartDiagCut

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem DiagNat_of : LateralTheory.E.PartDiagCut.DiagNat := by
  intro B _ I P Q h
  apply RingHom.ext
  intro b
  funext e
  simp only [stageMap, βP, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  exact (IsLocalization.map_eq (S := Localization (S I (par h e).1)) _ b).trans (by rfl)

end LateralTheory.E.DiagNatPf
