import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpenGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.VerticalUnit.finite_coheight_one_notMem` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteCoheightOneNotMemOpenGenericPoint.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.finite_coheight_one_notMem_open_genericPoint : ∀ (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (S : Set X), IsOpen S → genericPoint X ∈ S → {x : X | Order.coheight x = 1 ∧ x ∉ S}.Finite := by
  first | exact @GlobalTheory.VerticalUnit.finite_coheight_one_notMem | exact GlobalTheory.VerticalUnit.finite_coheight_one_notMem | (intros; apply GlobalTheory.VerticalUnit.finite_coheight_one_notMem <;> assumption)
