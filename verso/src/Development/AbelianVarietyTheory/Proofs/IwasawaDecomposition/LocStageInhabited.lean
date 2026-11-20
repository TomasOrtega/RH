import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

open Formalism Formalism.BasicNotions

namespace GlobalTheory.Mem

/- English proof (translation)
Use `choose P AI hT using GlobalTheory.MemLoc.exists_locPrime_tied`. Conclude with `⟨{ loc := fun l _ => P l, locA := fun l _ => AI l, locT := fun l _ => (hT l).some }⟩`.
-/
theorem locStage_inhabited : Nonempty GlobalTheory.Mem.LocStage := by
  classical
  choose P AI hT using GlobalTheory.MemLoc.exists_locPrime_tied
  exact ⟨{ loc := fun l _ => P l, locA := fun l _ => AI l, locT := fun l _ => (hT l).some }⟩

end GlobalTheory.Mem
