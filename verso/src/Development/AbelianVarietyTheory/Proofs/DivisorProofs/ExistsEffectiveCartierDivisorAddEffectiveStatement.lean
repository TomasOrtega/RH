import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorAddEffective
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsEffectiveCartierDivisorAddEffective.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.exists_effective_cartierDivisor_add_effective : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (H : LB X), IsAmpleLB H → ∀ D : CartierDiv X, ∃ E : CartierDiv X, E.Eff ∧ (D + E).Eff := by
  first | exact @GlobalTheory.Cartier.EffDiff.exists_eff_and_add_eff | exact GlobalTheory.Cartier.EffDiff.exists_eff_and_add_eff | (intros; apply GlobalTheory.Cartier.EffDiff.exists_eff_and_add_eff <;> assumption)
