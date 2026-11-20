import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScale
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTrueScaleIsScale.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.cdScaleIs_trueScale' : ∀ cd : CDHaar, CdScaleIs cd (trueScale cd) := by
  first | exact @GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale | exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale | (intros; apply GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale <;> assumption)
