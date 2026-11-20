import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricDenominatorOfZetaDenominators
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FToricDenominatorOfZetaDenominators.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.toric_denominator_of_zeta_denominators : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → LatIntRam → LatIntUnr → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator := by
  first | exact @GlobalTheory.ToricDenomRow.toricDenominator | exact GlobalTheory.ToricDenomRow.toricDenominator | (intros; apply GlobalTheory.ToricDenomRow.toricDenominator <;> assumption)
