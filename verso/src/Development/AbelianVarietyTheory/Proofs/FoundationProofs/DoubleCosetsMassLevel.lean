import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefClassDecompIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAndMass

namespace GlobalTheory.DefiniteDecompObj

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

/- English proof (translation)
The claim follows from `GlobalTheory.DefiniteDecomp.defClassDecomp`.
-/
theorem doubleCosets_mass : ∀ D : D7, DefClassDecomp D :=
  GlobalTheory.DefiniteDecomp.defClassDecomp

end GlobalTheory.DefiniteDecompObj
