import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEllipticKeyDataValueEqDiscriminant
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FThetaLawProofs%2FExistsEllipticKeyDataValueEqDiscriminant.lean&line=271#L271)
-/
theorem _root_.GlobalTheory.T.exists_ellipticKeyData_value_eq_discriminant : ThetaUnifAV → ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic], ∃ x : KeyIn R, x.P.g = 1 ∧ ∀ (s : R →+* ℂ) (x' : KeyIn ℂ) (τ M : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (a b : Fin x'.P.g → ℂ) (c : ℂ), KeyPB x' x s → charHalf x'.P.g a b → c ≠ 0 → NormalAt x' τ M a b c → M.det ^ 4 / c ^ 8 = s W.Δ := by
  first | exact @GlobalTheory.EllipticKey.exists_keyIn_value_eq_discriminant | exact GlobalTheory.EllipticKey.exists_keyIn_value_eq_discriminant | (intros; apply GlobalTheory.EllipticKey.exists_keyIn_value_eq_discriminant <;> assumption)
