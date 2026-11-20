import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LabelTorsion.pow_eq_one_of_over_label` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUniformisedPointOverLabelPowRNEqOne.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (b : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left → x ^ (S.r * S.N) = 1 := by
  first | exact @GlobalTheory.LabelTorsion.pow_eq_one_of_over_label | exact GlobalTheory.LabelTorsion.pow_eq_one_of_over_label | (intros; apply GlobalTheory.LabelTorsion.pow_eq_one_of_over_label <;> assumption)
