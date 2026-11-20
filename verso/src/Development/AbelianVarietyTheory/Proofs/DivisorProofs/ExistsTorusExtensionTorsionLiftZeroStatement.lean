import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusExtensionTorsionLiftZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorsLiftRoot.exists_qk_zero_of_pow_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsTorusExtensionTorsionLiftZero.lean&line=130#L130)
-/
theorem _root_.GlobalTheory.T.exists_torusExtension_torsion_lift_zero : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (n : ℕ), 1 ≤ n → ∀ (c' : D.X → (𝟙_ (Over (Sp R)) ⟶ D.P.A)), (∀ χ, c' χ ^ n = D.c χ) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (b : TF (R := R) F ⟶ D.P.A), b ^ n = 1 → ∃ p : QkPt D F n, p.y = 0 ∧ p.g.b = b := by
  first | exact @GlobalTheory.TorsLiftRoot.exists_qk_zero_of_pow_eq | exact GlobalTheory.TorsLiftRoot.exists_qk_zero_of_pow_eq | (intros; apply GlobalTheory.TorsLiftRoot.exists_qk_zero_of_pow_eq <;> assumption)
