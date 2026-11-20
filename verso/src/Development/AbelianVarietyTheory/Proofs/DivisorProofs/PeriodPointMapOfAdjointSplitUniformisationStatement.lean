import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPointMapOfAdjointSplitUniformisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.PowData.periodRel_of_adj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPeriodPointMapOfAdjointSplitUniformisation.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.periodPoint_map_of_adjoint_split_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (h : D₀.toPre.X →+ D.toPre.X) (k : D.toPre.X →+ D₀.toPre.X), Lin U.toUnifPre U₀.toUnifPre q qB h → OnTorus U₀.toUnifPre U.toUnifPre j k → (∀ y, D₀.toPre.c (k y) = D.toPre.c y ≫ qB) ∧ PeriodRel D.toPre D₀.toPre qB h k := by
  first | exact @GlobalTheory.Mum.PowData.periodRel_of_adj | exact GlobalTheory.Mum.PowData.periodRel_of_adj | (intros; apply GlobalTheory.Mum.PowData.periodRel_of_adj <;> assumption)
