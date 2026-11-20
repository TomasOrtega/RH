import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowstLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `R _ r n ν g f hf`. Rewrite `hf`, the goal using `[rowst_mem_dualWeyl_iff]`. Take `⟨hw, hc⟩` from `hf`. Use `⟨isWH_algHom (rowAct R g) (colW r n) (colW r n) (rowAct_X_isWH g) hw, ?_⟩` and prove the remaining obligations. Introduce `l j hlj`.

Rewrite using `[colAddGen_rowAct, rename_rowAct, hc l j hlj]`.
-/
theorem dualWeylModuleRowActionStable : DualWeylRowStable := by
  intro R _ r n ν g f hf
  rw [rowst_mem_dualWeyl_iff] at hf ⊢
  obtain ⟨hw, hc⟩ := hf
  refine ⟨isWH_algHom (rowAct R g) (colW r n) (colW r n)
    (rowAct_X_isWH g) hw, ?_⟩
  intro l j hlj
  rw [colAddGen_rowAct, rename_rowAct, hc l j hlj]

end Formalism.GradedWeylDivisibility
