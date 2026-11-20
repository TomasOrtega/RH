import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealGeneratedByOneAlmostEverywhere
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FFractionalIdealGeneratedByOneAlmostEverywhere.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.fractionalIdeal_generated_by_one_almostEverywhere : ∀ (D : D7) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), I ≠ 0 → ∃ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ S, ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ ((c : D.host.F) : D.host.E) ∈ I ∧ ∀ b ∈ I, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = (o : D.host.E) := by
  first | exact @GlobalTheory.IdeleGen.aeGen | exact GlobalTheory.IdeleGen.aeGen | (intros; apply GlobalTheory.IdeleGen.aeGen <;> assumption)
