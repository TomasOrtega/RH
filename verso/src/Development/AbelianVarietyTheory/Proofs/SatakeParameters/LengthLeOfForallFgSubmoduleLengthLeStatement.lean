import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthLeOfForallFgSubmoduleLengthLe
import Mathlib
open Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLengthLeOfForallFgSubmoduleLengthLe.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.length_le_of_forall_fg_submodule_length_le : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (b : ℕ∞), (∀ N : Submodule O M, N.FG → Module.length O N ≤ b) → Module.length O M ≤ b := by
  first | exact @GlobalTheory.length_le_of_forall_fg_length_le | exact GlobalTheory.length_le_of_forall_fg_length_le | (intros; apply GlobalTheory.length_le_of_forall_fg_length_le <;> assumption)
