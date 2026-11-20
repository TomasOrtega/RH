import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightRestDegreeAfterGapsBounds
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FWeightRestDegreeAfterGapsBounds.lean&line=247#L247)
-/
theorem _root_.GlobalTheory.T.weight_rest_degree_after_gaps_bounds : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), T.Q.Pins → ∀ j : ℕ, InR D j →
  0 ≤ restOf (numOf D L) (T.Q.Dw j) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) ∧
  (Tp.TO : ℝ) * restOf (numOf D L) (T.Q.Dw j) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) ≤ 100 * (D.R.f * D.R.k * ((numOf D L).Sc + (numOf D L).eta)) := by
  first | exact @GlobalTheory.RestDegree.rest_degree_bounds | exact GlobalTheory.RestDegree.rest_degree_bounds | (intros; apply GlobalTheory.RestDegree.rest_degree_bounds <;> assumption)
