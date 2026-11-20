import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceWeightOfTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RefSum.ToWeight.refW_of_refTheta` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FReferenceWeightOfTheta.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.reference_weight_of_theta : Hypotheses2 → Size → FlatDeg → RefTheta → RefW := by
  first | exact @GlobalTheory.RefSum.ToWeight.refW_of_refTheta | exact GlobalTheory.RefSum.ToWeight.refW_of_refTheta | (intros; apply GlobalTheory.RefSum.ToWeight.refW_of_refTheta <;> assumption)
