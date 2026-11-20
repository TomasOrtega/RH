import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount

namespace GlobalTheory.CompanionTheory.HeckeEnd

open PositivityTheory.Rg.BcB.F.Tail.PExp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem hkE_fin : HkEFin := by
  intro G V _ _ _ ρ K f hf v
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.hkE PositivityTheory.Rg.BcB.F.Tail.PExp.hkS
  rw [finsum_eq_sum_of_support_subset (s := hf.toFinset),
    finsum_eq_sum_of_support_subset (s := hf.toFinset), LinearMap.sum_apply]
  · rfl
  all_goals
    intro q hq
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h
    rw [Function.mem_support] at hq
    exact hq (by simp [h])

end GlobalTheory.CompanionTheory.HeckeEnd
