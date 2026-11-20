import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfFiniteRetractOfFiniteFlat
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.retract_flat_of_finite` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatOfFiniteRetractOfFiniteFlat.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.flat_of_finite_retract_of_finite_flat : ∀ (R : Type) [CommRing R] (H K : Over (Sp R)) (s : H ⟶ K) (r : K ⟶ H), s ≫ r = 𝟙 H → IsFinite H.hom → IsFinite K.hom → Flat K.hom → Flat H.hom := by
  first | exact @GlobalTheory.retract_flat_of_finite | exact GlobalTheory.retract_flat_of_finite | (intros; apply GlobalTheory.retract_flat_of_finite <;> assumption)
