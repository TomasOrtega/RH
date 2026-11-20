import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniversalChartPointsOverFieldPoint
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlphaPair.jetUniv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FUniversalChartPointsOverFieldPoint.lean&line=192#L192)
-/
theorem _root_.GlobalTheory.T.universalChart_points_over_field_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω) (P : PtFam (spMap β) t.G d), IsJetPt β x P → IsPtUniv (spMap β) t.G P := by
  first | exact @GlobalTheory.AlphaPair.jetUniv | exact GlobalTheory.AlphaPair.jetUniv | (intros; apply GlobalTheory.AlphaPair.jetUniv <;> assumption)
