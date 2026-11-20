import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulRowsScaledWeightLeKappaRows
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FMulRowsScaledWeightLeKappaRows.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.mul_rows_scaledWeight_le_kappaRows : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ) (τ : D.what₂.Tau), (∀ i, Tp.TO * (lR Tp hK j).aP τ i ≤ (kaR Tp hK j).aP τ i) ∧ (∀ i, Tp.TO * (lR Tp hK j).aM τ i ≤ (kaR Tp hK j).aM τ i) ∧ Tp.TO * WeightAlgebra.DF (lR Tp hK j) ≤ WeightAlgebra.DF (kaR Tp hK j) := by
  first | exact @GlobalTheory.RunDepth.mul_rows_lR_le_kaR | exact GlobalTheory.RunDepth.mul_rows_lR_le_kaR | (intros; apply GlobalTheory.RunDepth.mul_rows_lR_le_kaR <;> assumption)
