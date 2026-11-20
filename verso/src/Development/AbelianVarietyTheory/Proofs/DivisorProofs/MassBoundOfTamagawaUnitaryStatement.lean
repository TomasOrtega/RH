import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassBoundOfTamagawaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UCls.massBound_of_tamagawa` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMassBoundOfTamagawaUnitary.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.mass_bound_of_tamagawa_unitary : GlobalTheory.Published.TamagawaSpecialUnitary → GlobalTheory.UCls.MassBound := by
  first | exact @GlobalTheory.UCls.massBound_of_tamagawa | exact GlobalTheory.UCls.massBound_of_tamagawa | (intros; apply GlobalTheory.UCls.massBound_of_tamagawa <;> assumption)
