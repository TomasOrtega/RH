import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSubstitutionIntegral.IntegralSubst

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.PhGram

open PI.FglGram

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem phGram_of (hC : Column) (hG : Gather) : PI.FglGram.PhGram := by
  intro p _ l ex ph S hD hsw hiM hiA hN hCj hB κ _ k A hA
  have H : Hyps l ex ph S := ⟨hD, hsw, hiM, hiA, hN, hCj, hB⟩
  exact hG p l ex ph S H (hC p l ex ph S H) κ k A hA

end PI.UnitaryGroupMassFormula.PhGram
