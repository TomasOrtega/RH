import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.MemAnnih
import Formalism.WachLatticeTwists.HodgeTateChains.CorrectedHypothesisWConsequences

open Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem jumps_of_dual_twist : JumpsOfDualTwist := by
  intro J
  constructor
  · simp only [jumpsDualTwist, Multiset.mem_toFinset, Multiset.mem_map, not_iff_not]
    constructor
    · rintro ⟨u, hu, h⟩
      have : u = -1 := by omega
      exact this ▸ hu
    · intro h
      exact ⟨-1, h, by norm_num⟩
  · rw [Finset.nonempty_iff_ne_empty]
    simp [jumpsDualTwist]

end Formalism.RepresentationBoundsCohomology.JT
