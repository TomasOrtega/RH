import Development.EtaleCohomology.EtaleSheaves.PartDiagCut

namespace LateralTheory.E.DiagNatPf
open LateralTheory.E.PartDiagCut

/- English proof (translation)
Introduce `B _ I P Q h`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `b`. Use function extensionality and compare the values at `e`. Simplify using `only [stageMap, βP, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]`.

Conclude with `(IsLocalization.map_eq (S := Localization (S I (par h e).1)) _ b).trans (by rfl)`.
-/
theorem DiagNat_of : LateralTheory.E.PartDiagCut.DiagNat := by
  intro B _ I P Q h
  apply RingHom.ext
  intro b
  funext e
  simp only [stageMap, βP, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  exact (IsLocalization.map_eq (S := Localization (S I (par h e).1)) _ b).trans (by rfl)

end LateralTheory.E.DiagNatPf
