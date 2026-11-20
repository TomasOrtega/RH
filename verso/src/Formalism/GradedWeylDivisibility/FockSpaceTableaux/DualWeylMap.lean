import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LSatLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `R S _ _ φ r n ν f hf`. Rewrite `hf`, the goal using `[lsat_mem_dualWeyl]`. Use `⟨lsat_isWH_map φ _ _ f hf.1, fun l j hlj => ?_⟩` and prove the remaining obligations. Rewrite using `[← lsat_map_colAddGen, hf.2 l j hlj, map_rename]`.
-/
theorem dualWeylModuleMap : DualWeylMap := by
  intro R S _ _ φ r n ν f hf
  rw [lsat_mem_dualWeyl] at hf ⊢
  refine ⟨lsat_isWH_map φ _ _ f hf.1, fun l j hlj => ?_⟩
  rw [← lsat_map_colAddGen, hf.2 l j hlj, map_rename]

end Formalism.GradedWeylDivisibility
