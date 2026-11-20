import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement

namespace ReciprocityTheory.ChartRestriction.DS.Lap

/- English proof (translation)
Introduce `k r u v b t`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Establish `ha` using `a.isLt`. Simplify using `only [lamT, raisePar]`.

Use `split_ifs`. Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `(exfalso; omega)`. Consider the case `(have h0 : a.val - (k - 1) = 0 := by omega`.

Simplify using `[h0])`. Use function extensionality and compare the values at `a`. Establish `ha` using `a.isLt`. Simplify using `only [raisePar, walkPar, parLam]`. Use `split_ifs`.

Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `(exfalso; omega)`. Use function extensionality and compare the values at `a`. Simplify using `[walkPar]`.
-/
theorem walkEnds : EndsStatement := by
  intro k r u v b t
  refine ⟨?_, ?_, ?_⟩
  · funext a
    have ha := a.isLt
    simp only [lamT, raisePar]
    split_ifs
    all_goals first
      | rfl
      | (exfalso; omega)
      | (have h0 : a.val - (k - 1) = 0 := by omega
         simp [h0])
  · funext a
    have ha := a.isLt
    simp only [raisePar, walkPar, parLam]
    split_ifs
    all_goals first
      | rfl
      | (exfalso; omega)
  · funext a
    simp [walkPar]

end ReciprocityTheory.ChartRestriction.DS.Lap
