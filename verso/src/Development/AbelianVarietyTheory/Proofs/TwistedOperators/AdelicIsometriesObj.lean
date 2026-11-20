import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometries

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links

namespace GlobalTheory.AdIsomObj

/- English proof (translation)
The claim follows from `GlobalTheory.AdIsom.adelicIsometries D`.
-/
theorem adelicIsometries_obj (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.AdelicIsometries D :=
  GlobalTheory.AdIsom.adelicIsometries D

/- English proof (translation)
The claim follows from `(adelicIsometries_obj D).2.2.2.2.2.2.2.2.2.2.2.1 V N`.
-/
theorem frames_exist (D : D7) (V : HSp D) (N : ℕ) : ∃ β Λ, IsSDFrame V β Λ N :=
  (adelicIsometries_obj D).2.2.2.2.2.2.2.2.2.2.2.1 V N

end GlobalTheory.AdIsomObj

end
