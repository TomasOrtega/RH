import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
import ReciprocityTheory.NeutralLocalFields.HilbertClassField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FHilbertClassFieldOfGlobalArtinReciprocity.lean&line=255#L255)
-/
theorem _root_.GlobalTheory.T.hilbertClassField_of_globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → Neutral.HilbertClassField.Statement := by
  first | exact @GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField | exact GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField | (intros; apply GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField <;> assumption)
