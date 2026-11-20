import Mathlib
import Formalism.PeriodIntegrals.GaugeGap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IntInter

namespace PI.GaugeCharW

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem intInter : IntInter := by
  intro F _ _ a ha
  have h : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F a ≤ 1 := by
    intro v
    have h1 := ha v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a]
    exact h1
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F a h
  exact ⟨b, hb⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem openInt : OpenInt := by
  intro F _ _
  exact RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)

end PI.GaugeCharW
