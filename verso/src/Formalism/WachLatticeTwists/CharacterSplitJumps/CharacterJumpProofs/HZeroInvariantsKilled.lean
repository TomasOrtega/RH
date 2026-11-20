import Formalism.WachLatticeTwists.CharacterSplitJumps.WachTwistTheoremFromTorsionBound
import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.InChiSplit
import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.HZeroSplitAllPlaces
import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.PropLocBK

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem h_zero_invariants_killed : HZeroInvariantsKilled := by
  intro ℓ _ O _ G _ A _ _ ρA Dw Dat b w m U hsurj h z hz
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  obtain ⟨x, rfl⟩ := hsurj z hz
  rw [← transport (ℓ := ℓ) O b, h0 ℓ w m h1 h2 h3 U h4 h5 Dat h6 h7 h8 h9 h10 x, map_zero]

end Formalism.RepresentationBoundsCohomology.JT
