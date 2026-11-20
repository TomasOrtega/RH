import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
import Mathlib
import Formalism.HermitianLattices.StatementMass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FSiegelMassRatioUnimodularDefinite.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.siegel_massRatio_unimodular_definite : Formalism.HermitianLatticesTheory.SiegelMassRatio := by
  first | exact @GlobalTheory.Mass.siegelMassRatio_holds | exact GlobalTheory.Mass.siegelMassRatio_holds | (intros; apply GlobalTheory.Mass.siegelMassRatio_holds <;> assumption)
