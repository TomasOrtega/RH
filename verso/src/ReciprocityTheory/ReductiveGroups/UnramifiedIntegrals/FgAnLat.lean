import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.LatModel

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem good_lattice (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l])
    (hg : IsGoodModel l L ι g2 g3) :
    ∃ L' : PeriodPair, LatModel l L' ι g2 g3 ∧ ∀ d, HasCMBy d L → HasCMBy d L' := by
  obtain ⟨-, -, h2, h3, -, lam, hlam, e2, e3⟩ := hg
  have hm : ι.symm lam ≠ 0 := by
    intro h
    apply hlam
    have := congrArg ι h
    simpa using this
  have hc : (ι.symm lam)⁻¹ ≠ 0 := inv_ne_zero hm
  obtain ⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩ := F.homogeneity L (ι.symm lam)⁻¹ hc
  refine ⟨F.scalePair L (ι.symm lam)⁻¹ hc, ⟨?_, ?_, h2, h3⟩,
    fun d hd => F.hasCMByScale d L _ hc hd⟩
  · rw [hg2, e2]
    simp
  · rw [hg3, e3]
    simp

end ReciprocityTheory.ChartRestriction.L1
