import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem genusMassStd (D : D7) : GenusMassStd D :=
  GlobalTheory.DefiniteMass.mass_eq_massI D

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem genusMassStd_of_landherrHasse :
    (∀ D : D7, LandherrHasse D) → ∀ D : D7, GenusMassStd D :=
  fun _ D => genusMassStd D

end GlobalTheory
