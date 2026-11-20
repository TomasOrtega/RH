import Mathlib
import Formalism.PeriodIntegrals.GaugeGap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IntInter

namespace PI.GaugeCharW

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

/- English proof (translation)
Introduce `F _ _ a ha`. Establish `h : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F a ≤ 1`. Introduce `v`. Establish `h1` using `ha v`. Rewrite `h1` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`.

Rewrite using `[← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a]`. Conclude with `h1`. Take `⟨b, hb⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one F a h`. Conclude with `⟨b, hb⟩`.
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
Introduce `F _ _`. Conclude with `RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)`.
-/
theorem openInt : OpenInt := by
  intro F _ _
  exact RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)

end PI.GaugeCharW
