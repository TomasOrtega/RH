import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelFunctionFieldTrdegEqRelDim
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldMapCompCongr
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Vert.Model.trdeg_fnFld_eq_relDim_ofResidue` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FModelFunctionFieldTrdegEqRelDim.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.model_function_field_trdeg_eq_relDim : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : GlobalTheory.Vert.Model O), letI := Z.fnConst.toAlgebra; Algebra.trdeg O Z.fnFld = Z.relDim := by
  first | exact @GlobalTheory.Vert.Model.trdeg_fnFld_eq_relDim_ofResidue | exact GlobalTheory.Vert.Model.trdeg_fnFld_eq_relDim_ofResidue | (intros; apply GlobalTheory.Vert.Model.trdeg_fnFld_eq_relDim_ofResidue <;> assumption)
