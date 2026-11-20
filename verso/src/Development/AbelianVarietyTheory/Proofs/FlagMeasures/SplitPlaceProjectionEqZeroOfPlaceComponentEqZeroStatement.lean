import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceProjectionEqZeroOfPlaceComponentEqZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FSplitPlaceProjectionEqZeroOfPlaceComponentEqZero.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.splitPlaceProjection_eq_zero_of_placeComponent_eq_zero : ∀ (L : Type) [Field L] [NumberField L] (s : ReciprocityTheory.Aut.SplitPlace L) (a : ReciprocityTheory.Aut.AL L), ReciprocityTheory.Aut.compAt L s.v a = 0 → s.proj a = 0 := by
  first | exact @GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero | exact GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero | (intros; apply GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero <;> assumption)
