import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothProjectiveModel
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
/- English proof (citation)
Apply `GlobalTheory.BirModel.exists_smooth_projective_model` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSmoothProjectiveModel.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.exists_smooth_projective_birational_model : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (s : Y ⟶ X) (_ : IsDominant s), SmoothOfRelativeDimension n (s ≫ p) ∧ IsProjOver (s ≫ p) ∧ Function.Bijective (functionFieldMap s) := by
  first | exact @_root_.GlobalTheory.BirModel.exists_smooth_projective_model | exact _root_.GlobalTheory.BirModel.exists_smooth_projective_model | (intros; apply _root_.GlobalTheory.BirModel.exists_smooth_projective_model <;> assumption)
