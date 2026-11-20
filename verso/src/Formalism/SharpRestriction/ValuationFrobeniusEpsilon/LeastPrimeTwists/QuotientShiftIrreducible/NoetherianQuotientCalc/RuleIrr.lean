import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleFin

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

/- English proof (translation)
Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ruleIrr : RuleIrr := by
  rintro k X F hF ⟨N, hN⟩
  filter_upwards [hF.eventually_gr_le X.std X.iSup_eq_top N] with m hm
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  refine Submodule.smul_induction_on (hm y hy) ?_ ?_
  · intro a ha z _
    exact Module.mem_annihilator.1 (hN ha) z
  · intro x y hx hy
    rw [hx, hy, add_zero]

end Formalism.MainNotions.V.Pf.V2.Calc
