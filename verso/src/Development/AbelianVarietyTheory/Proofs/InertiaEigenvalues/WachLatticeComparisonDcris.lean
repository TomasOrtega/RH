import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmpIsoOfExpansions

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.CmpCris

/- English proof (translation)
Introduce `l _ K s LL h T hT`. Take `⟨h1, h2, -, h4⟩` from `cmp_iso D HW F Cm l K s LL h T hT`. Use `⟨fun x hx => ?_, h2, fun x k hk => h4 x k hk⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `(h1 x).1 hx`. Conclude with `⟨y, y.2, rfl⟩`.
-/
theorem wachLattice_comparison_dcris (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) : P3 D HW F Cm := by
  intro l _ K s LL h T hT
  obtain ⟨h1, h2, -, h4⟩ := cmp_iso D HW F Cm l K s LL h T hT
  refine ⟨fun x hx => ?_, h2, fun x k hk => h4 x k hk⟩
  obtain ⟨y, rfl⟩ := (h1 x).1 hx
  exact ⟨y, y.2, rfl⟩

end GlobalTheory.NL.CmpCris
