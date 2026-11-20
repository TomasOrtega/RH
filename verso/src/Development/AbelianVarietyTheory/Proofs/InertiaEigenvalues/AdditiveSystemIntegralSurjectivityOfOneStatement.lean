import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemIntegralSurjectivityOfOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMonE.glOnto_of_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAdditiveSystemIntegralSurjectivityOfOne.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.additiveSystemIntegralSurjectivity_of_one : ∀ N : ℕ, 1 ≤ N → GLOnto 1 → GLOnto N := by
  first | exact @GlobalTheory.PMonE.glOnto_of_one | exact GlobalTheory.PMonE.glOnto_of_one | (intros; apply GlobalTheory.PMonE.glOnto_of_one <;> assumption)
