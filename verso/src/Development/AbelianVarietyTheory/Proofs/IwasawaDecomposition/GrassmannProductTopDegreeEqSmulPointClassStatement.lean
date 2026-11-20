import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductTopDegreeEqSmulPointClass
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FGrassmannProductTopDegreeEqSmulPointClass.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.grassmannProduct_topDegree_eq_smul_pointClass : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), IsWeightedHomogeneous Prod.snd Q (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) → ∃ c : ℝ, Q - C c * pointPoly H Dw ∈ relIdeal H Dw := by
  first | exact @GlobalTheory.GrassTopDim.top_eq_smul_point | exact GlobalTheory.GrassTopDim.top_eq_smul_point | (intros; apply GlobalTheory.GrassTopDim.top_eq_smul_point <;> assumption)
