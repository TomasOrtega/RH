import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataPeriodDiagonalMemMaxIdealMulGene
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDegenerationDataPeriodDiagonalMemMaxIdealMulGene.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.degenerationData_period_diagonal_mem_maxIdeal_mul_generator : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (y : D.toPre.X), y ≠ 0 → ∃ r ∈ maximalIdeal V, ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = algebraMap V _ r ∧ ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (lamPts (D.toPre.c y) (D.toPre.c y)) negε), ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (TK V).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val (D.toPre.tau y y) ρ z J = gm ρ z ⊤ (unitOn k) * val u (ρ ≫ jK V) z J := by
  first | exact @GlobalTheory.DataPos.tau_diag_pos | exact GlobalTheory.DataPos.tau_diag_pos | (intros; apply GlobalTheory.DataPos.tau_diag_pos <;> assumption)
