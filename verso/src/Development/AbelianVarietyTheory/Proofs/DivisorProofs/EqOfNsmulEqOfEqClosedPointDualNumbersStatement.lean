import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNsmulEqOfEqClosedPointDualNumbers
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEqOfNsmulEqOfEqClosedPointDualNumbers.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.eq_of_nsmul_eq_of_eq_closedPoint_dualNumbers : ∀ (k : Type) [Field k] (B : Over (Sp (DualNumber k))) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : k) ≠ 0 → ∀ x x' : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B, x ^ n = x' ^ n → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x.left = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x'.left → x = x' := by
  first | exact @GlobalTheory.UCanon.eq_of_pow_eq_of_eq_at_closed | exact GlobalTheory.UCanon.eq_of_pow_eq_of_eq_at_closed | (intros; apply GlobalTheory.UCanon.eq_of_pow_eq_of_eq_at_closed <;> assumption)
