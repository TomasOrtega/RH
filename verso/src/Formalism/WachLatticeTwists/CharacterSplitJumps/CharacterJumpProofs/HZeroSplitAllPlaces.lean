import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.MemAnnih
import Formalism.WachLatticeTwists.HodgeTateChains.CorrectedHypothesisWConsequences

open Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

/- English proof (translation)
Introduce `J`. Prove the components needed by the constructor for the conclusion. Simplify using `only [jumpsDualTwist, Multiset.mem_toFinset, Multiset.mem_map, not_iff_not]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, h⟩`.

Establish `: u = -1` using `by omega`. Conclude with `this ▸ hu`. Introduce `h`. Conclude with `⟨-1, h, by norm_num⟩`. Rewrite using `[Finset.nonempty_iff_ne_empty]`.

Simplify using `[jumpsDualTwist]`.
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
