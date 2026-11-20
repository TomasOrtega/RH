import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RulePos

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

open E4 in

/- English proof (translation)
Introduce `k X ts F' F F'' hv hF' hF hF'' S hA`. Establish `hle : F.Ann ≤ F'.Ann`. Introduce `a ha`. Use `Module.mem_annihilator.mpr fun x => S.inj ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_zero]`.

Conclude with `Module.mem_annihilator.mp ha _`. Establish `h1` using `Pos.e1 k X ts F' F F'' hv hF' hF hF'' S hA`. Establish `h2` using `rulePos k X ts F' hv hF' (admissible_mono_ideal X.𝒜 hle hA)`. Use `filter_upwards [h1, h2] with m a b`. Rewrite using `[a]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ruleMono : RuleMono := by
  intro k X ts F' F F'' hv hF' hF hF'' S hA
  have hle : F.Ann ≤ F'.Ann := by
    intro a ha
    refine Module.mem_annihilator.mpr fun x => S.inj ?_
    rw [map_smul, map_zero]
    exact Module.mem_annihilator.mp ha _
  have h1 := Pos.e1 k X ts F' F F'' hv hF' hF hF'' S hA
  have h2 := rulePos k X ts F' hv hF' (admissible_mono_ideal X.𝒜 hle hA)
  filter_upwards [h1, h2] with m a b
  rw [a]
  linarith

end Formalism.MainNotions.V.Pf.V2.Calc
