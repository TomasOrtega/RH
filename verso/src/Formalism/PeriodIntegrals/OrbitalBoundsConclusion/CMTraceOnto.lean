import Mathlib
import Formalism.PeriodIntegrals.CMTraceOnto
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMTraceSurjective.IsTrMulConjOfMem

/- English proof (translation)
Introduce `K _ _ _ hK a ha`. Establish `hfix : PI.CMT.conj a = a`. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[PI.CMT.coe_conj, ha]`. Take `⟨x, hx⟩` from `PI.CMT.isTr_mul_fixed hfix (PI.CMT.isTr_one hK.2.2)`.

Use `⟨x, PI.CMT.conj x, PI.CMT.coe_conj x, ?_⟩` and prove the remaining obligations. Rewrite using `[hx, mul_one]`.
-/
theorem traceSurjective_holds : PI.CMTraceOnto := by
  intro K _ _ _ hK a ha

  have hfix : PI.CMT.conj a = a := by
    apply NumberField.RingOfIntegers.ext
    rw [PI.CMT.coe_conj, ha]
  obtain ⟨x, hx⟩ := PI.CMT.isTr_mul_fixed hfix (PI.CMT.isTr_one hK.2.2)
  refine ⟨x, PI.CMT.conj x, PI.CMT.coe_conj x, ?_⟩
  rw [hx, mul_one]
