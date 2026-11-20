import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement

namespace ReciprocityTheory.ChartRestriction.DS.Lap

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules.

Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
