import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField

noncomputable section

open GlobalTheory.StdUnn

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pIn : PIn := by
  intro D n p hp
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
  obtain ⟨m, u, b, e, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hp a ha
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr (Or.inl ⟨_, _, hm⟩)))
    (Subgroup.subset_closure (Or.inl ⟨b, hu⟩))

end PositivityTheory.Rg.Sw.Glob
