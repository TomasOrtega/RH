import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVDimEqOfGrpPullbackField
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPolAVDimEqOfGrpPullbackField.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.polAV_dim_eq_of_grpPullback_field : ∀ (K : Type) [Field K] (T : Scheme.{0}) (P : PolAV T) (P₀ : PolAV (Sp K)) (f : Sp K ⟶ T) (a : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A f a → P₀.g = P.g := by
  first | exact @GlobalTheory.polAV_g_eq_of_isGrpPullback | exact GlobalTheory.polAV_g_eq_of_isGrpPullback | (intros; apply GlobalTheory.polAV_g_eq_of_isGrpPullback <;> assumption)
