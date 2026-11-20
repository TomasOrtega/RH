import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoCompCartesianHomValues
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsMumfordBundleIsoCompCartesianHomValues.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.exists_mumfordBundleIso_comp_cartesianHom_values : ∀ {S S' S₁ : Scheme.{0}} {B : Over S₁} {G : Over S} {G' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {M : LB B.left} {L : LB G.left} {L' : LB G'.left} {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f φ) {β₂ : (G2 G).left ⟶ (G2 B).left}, M.IsLB → L.IsLB → L'.IsLB → ∀ (w : LB.Iso (abelian₂ G L) ((abelian₂ B M).pull β₂)) (v : LB.Iso L' (L.pull φ)), w.IsGen → v.IsGen → ∃ w'' : LB.Iso (abelian₂ G' L') ((abelian₂ B M).pull (sqOf gp ≫ β₂)), w''.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w'' p z J J' = lamVal w (p ≫ sqOf gp) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  first | exact @GlobalTheory.TautPull.lamIso_comp_exists | exact GlobalTheory.TautPull.lamIso_comp_exists | (intros; apply GlobalTheory.TautPull.lamIso_comp_exists <;> assumption)
