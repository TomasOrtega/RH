import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentLinearCombinationIsTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTangentLinearCombinationIsTangent.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.tangent_linear_combination_isTangent : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (m : ℕ) (v : Fin m → (epsR R ⟶ G)) (c : Fin m → R), (∀ i, IsTangent (v i)) → IsTangent (tanComb c v) := by
  first | exact @GlobalTheory.SecJet.isTangent_tanComb | exact GlobalTheory.SecJet.isTangent_tanComb | (intros; apply GlobalTheory.SecJet.isTangent_tanComb <;> assumption)
