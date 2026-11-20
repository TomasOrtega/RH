import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelModuliTraitThroughCompactificationPt
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TChart.exists_trait_at` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSiegelModuliTraitThroughCompactificationPt.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.exists_siegelModuli_trait_through_compactification_pt : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) [LocallyOfFiniteType s] [IsLocallyNoetherian S] (j : F.X ⟶ S) [IsOpenImmersion j], 3 ≤ n → Dense (Set.range j) → j ≫ s = F.s → ∀ x : S, ∃ (T : GlobalTheory.Poinc.Trait F) (ξT : Sp T.V ⟶ S) (b : cycAway n →+* T.V), ξT (closedPoint T.V) = x ∧ jK T.V ≫ ξT = T.y ≫ j ∧ ξT ≫ s = spMap b := by
  first | exact @GlobalTheory.TChart.exists_trait_at | exact GlobalTheory.TChart.exists_trait_at | (intros; apply GlobalTheory.TChart.exists_trait_at <;> assumption)
