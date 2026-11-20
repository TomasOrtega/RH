import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkPairingExistsUniqueTorus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
/- English proof (citation)
Apply `GlobalTheory.weilQk_existsUnique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUniformizationProofs%2FWeilQkPairingExistsUniqueTorus.lean&line=185#L185)
-/
theorem _root_.GlobalTheory.T.weilQk_pairing_existsUnique_torus : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, (∃! ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ) ∧ ∀ t, p.y = 0 → IsTor t p.g → WeilQkIs D.toPre F k p p' (t (Multiplicative.ofAdd p'.y)).val := by
  first | exact @GlobalTheory.weilQk_existsUnique | exact GlobalTheory.weilQk_existsUnique | (intros; apply GlobalTheory.weilQk_existsUnique <;> assumption)
