import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryOfFiniteIndex

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.FiniteRestrictionH1f

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem mem_H1f_iff_res_mem : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Pr2b D HW F := by
  intro D HW F l _ K s LL h T _ κ
  have hfin := GKs_finiteIndex (D.loc l) K LL _ ((HW l).W K s LL h)
  refine (mem_H1fT_iff_res ((D.loc l).PD K) T ((HW l).W K s LL h).GKs κ).trans ?_
  constructor
  · rintro ⟨c, hx, hc⟩
    exact ⟨c, ⟨c.2, c.2.1, hx⟩, hc⟩
  · rintro ⟨c, ⟨-, -, hx⟩, hc⟩
    exact ⟨c, hx, hc⟩

end GlobalTheory.NL.FiniteRestrictionH1f
