import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBoundOfHeightPublished
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValVwProdLe

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt GlobalTheory.CovTop
attribute [local instance] Over.cartesianMonoidalCategory

attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovHt.HTLatB.latBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeBoundOfHeightPublished.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.lattice_bound_of_height : Hypotheses2 → GlobalTheory.CovHt.HTDiag.LatBound := by
  first | exact @GlobalTheory.CovHt.HTLatB.latBound | exact GlobalTheory.CovHt.HTLatB.latBound | (intros; apply GlobalTheory.CovHt.HTLatB.latBound <;> assumption)
