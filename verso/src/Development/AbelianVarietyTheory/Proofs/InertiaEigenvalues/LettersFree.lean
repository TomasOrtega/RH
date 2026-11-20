import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLetterBasis

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.LetterFree

/- English proof (translation)
Introduce `D HW F l _ K s LL h T hT`. Take `⟨hd, -, hb⟩` from `letters_loc (HW l) K s LL h T hT`. Use `⟨hd.2.symm, fun i => ?_⟩` and prove the remaining obligations. Take `⟨b, hb1, hb2⟩` from `hb i`. Conclude with `⟨_, b, hb1, hb2⟩`.
-/
theorem letters_free : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), WachLatticeFreeGlobal D HW F := by
  intro D HW F l _ K s LL h T hT
  obtain ⟨hd, -, hb⟩ := letters_loc (HW l) K s LL h T hT
  refine ⟨hd.2.symm, fun i => ?_⟩
  obtain ⟨b, hb1, hb2⟩ := hb i
  exact ⟨_, b, hb1, hb2⟩

end GlobalTheory.NL.LetterFree
