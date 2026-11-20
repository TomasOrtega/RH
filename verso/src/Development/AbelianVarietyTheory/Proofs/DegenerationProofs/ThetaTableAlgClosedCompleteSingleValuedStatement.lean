import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTableAlgClosedCompleteSingleValued
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.tab_full_uniq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FThetaTableAlgClosedCompleteSingleValued.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.thetaTable_algClosed_complete_singleValued : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m n r : ℕ), Odd m → Odd n → ∀ (th : SecA A F 1) (τ : Fin r → SecA A F (m ^ 2)), (∀ t, ∃! a, Cmb τ a t) → (tab ρ m th τ).Full (m ^ 2) n ∧ (tab ρ m th τ).Uniq (m ^ 2) n := by
  first | exact @GlobalTheory.tab_full_uniq | exact GlobalTheory.tab_full_uniq | (intros; apply GlobalTheory.tab_full_uniq <;> assumption)
