import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralIdempotentSplitPlaceCmFiniteAdeles
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsIntegralIdempotentSplitPlaceCmFiniteAdeles.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.exists_integralIdempotent_splitPlace_cmFiniteAdeles : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L), ∃ ε : ReciprocityTheory.Aut.AL L, ε * ε = ε ∧ ε * ReciprocityTheory.Aut.conjAL L ε = 0 ∧ ε ∈ ReciprocityTheory.Aut.ALint L ∧ s.proj ε = 1 ∧ ReciprocityTheory.Aut.compAt L s.v (ε + ReciprocityTheory.Aut.conjAL L ε) = 1 ∧ ∀ v, v ≠ s.v → ReciprocityTheory.Aut.compAt L v ε = 0 ∧ ReciprocityTheory.Aut.compAt L v (ReciprocityTheory.Aut.conjAL L ε) = 0 := by
  first | exact @GlobalTheory.SplitIdem.exists_idem | exact GlobalTheory.SplitIdem.exists_idem | (intros; apply GlobalTheory.SplitIdem.exists_idem <;> assumption)
