import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerPolarisedAbelianField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsVeryAmpleFourthPowerPolarisedAbelianField.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.exists_veryAmple_fourthPower_polarisedAbelian_field : AmpleSt → ∀ (K : Type) [Field K] (P : PolAV (Sp K)), ∃ (m : ℕ) (b : Fin (m + 1) → H0 P.L 4), VeryAmpleAlong P.A.hom (𝟙 P.A.left) P.L b := by
  first | exact @GlobalTheory.Mum.veryAmpleAlong_field | exact GlobalTheory.Mum.veryAmpleAlong_field | (intros; apply GlobalTheory.Mum.veryAmpleAlong_field <;> assumption)
