import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TraceFormEquality.FormEqImage

/- English proof (translation)
Introduce `K _ σ G _ _ T P0 hM EE _ _ ρE M M' h`. Establish `h1 : M.form 1 = M'.form 1`. Rewrite using `[PI.Dv.HermitianFormEquivalence.form_one_eq M P0 hM, PI.Dv.HermitianFormEquivalence.form_one_eq M' P0 hM, h]`. Use `⟨h1, fun P => ?_⟩` and prove the remaining obligations. Rewrite using `[PI.Dv.HermitianFormEquivalence.form_eq_image M, PI.Dv.HermitianFormEquivalence.form_eq_image M', h1]`.
-/
theorem division_form_eq : PI.Dv.SameFormAllLevels := by
  intro K _ σ G _ _ T P0 hM EE _ _ ρE M M' h
  have h1 : M.form 1 = M'.form 1 := by
    rw [PI.Dv.HermitianFormEquivalence.form_one_eq M P0 hM, PI.Dv.HermitianFormEquivalence.form_one_eq M' P0 hM, h]
  refine ⟨h1, fun P => ?_⟩
  rw [PI.Dv.HermitianFormEquivalence.form_eq_image M, PI.Dv.HermitianFormEquivalence.form_eq_image M', h1]
