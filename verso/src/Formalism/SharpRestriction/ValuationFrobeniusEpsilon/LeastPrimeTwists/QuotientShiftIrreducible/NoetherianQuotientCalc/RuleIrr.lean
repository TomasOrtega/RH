import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleFin

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

/- English proof (translation)
Introduce and unpack `k X F hF ⟨N, hN⟩`. Use `filter_upwards [hF.eventually_gr_le X.std X.iSup_eq_top N] with m hm`. Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Rewrite using `[Submodule.mem_bot]`.

Use `Submodule.smul_induction_on (hm y hy) ?_ ?_` and prove the remaining obligations. Introduce `a ha z _`. Conclude with `Module.mem_annihilator.1 (hN ha) z`. Introduce `x y hx hy`. Rewrite using `[hx, hy, add_zero]`.
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
