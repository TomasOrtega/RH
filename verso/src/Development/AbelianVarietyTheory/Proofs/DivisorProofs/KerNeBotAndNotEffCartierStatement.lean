import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerNeBotAndNotEffCartier
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKerNeBotAndNotEffCartier.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.ker_ne_bot_and_not_effCartier_of_two_le_dim : ∀ {W Y : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian Y] (i : W ⟶ Y) [IsClosedImmersion i], 2 ≤ ringKrullDim (Y.presheaf.stalk (i (genericPoint W))) → i.ker ≠ ⊥ ∧ ∀ U : Y.Opens, i (genericPoint W) ∈ U → ¬ FinalTheorems.EffCartier (i.ker.comap U.ι) := by
  first | exact @GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier | exact GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier | (intros; apply GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier <;> assumption)
