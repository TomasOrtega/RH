import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfData
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FContinuousIotaOQOfData.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.continuous_iotaOQ' : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc), Continuous (iotaOQ N A i) := by
  first | exact @GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data | exact GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data | (intros; apply GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data <;> assumption)
