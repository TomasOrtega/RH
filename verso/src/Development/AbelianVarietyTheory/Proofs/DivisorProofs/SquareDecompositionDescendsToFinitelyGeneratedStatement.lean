import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionDescendsToFinitelyGenerated
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SqDecSpread.sqDec_fg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSquareDecompositionDescendsToFinitelyGenerated.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.squareDecomposition_descends_to_finitelyGenerated : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (algebraMap k Ω))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω)))) → ∃ R : Subalgebra k Ω, R.FG ∧ SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) := by
  first | exact @GlobalTheory.SqDecSpread.sqDec_fg | exact GlobalTheory.SqDecSpread.sqDec_fg | (intros; apply GlobalTheory.SqDecSpread.sqDec_fg <;> assumption)
