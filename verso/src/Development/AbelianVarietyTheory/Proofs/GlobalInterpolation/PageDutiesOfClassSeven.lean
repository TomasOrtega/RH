import Mathlib
import Formalism.SharpRestriction.PageFix
import Formalism.SharpRestriction.LevelLetterCocycles.AlignN
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices

namespace GlobalTheory.EX.DQ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem tameList_eq {g m : ℕ} (χ : Fin m → (ZMod g)ˣ) : DC.tameList χ = Formalism.MainNotions.tameList χ := by
  funext o
  rcases o with _ | ⟨j, _ | _⟩ <;> rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem tameDistinct_iff (r g : ℕ) [Fact g.Prime] {m : ℕ} (χ : Fin m → (ZMod g)ˣ) :
    DC.TameDistinct r g χ ↔ Formalism.MainNotions.TameDistinct r g χ := by
  unfold DC.TameDistinct Formalism.MainNotions.TameDistinct
  rw [tameList_eq]

end GlobalTheory.EX.DQ
