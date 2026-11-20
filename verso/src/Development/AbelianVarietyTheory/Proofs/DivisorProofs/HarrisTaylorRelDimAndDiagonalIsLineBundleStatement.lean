import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTDim.relDim_and_isLB` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHarrisTaylorRelDimAndDiagonalIsLineBundle.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), SmoothOfRelativeDimension D.g o.A.hom ∧ (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := by
  first | exact @GlobalTheory.HTDim.relDim_and_isLB | exact GlobalTheory.HTDim.relDim_and_isLB | (intros; apply GlobalTheory.HTDim.relDim_and_isLB <;> assumption)
