import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedOfIsPullbackUniversallyClosedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isSeparated_of_isPullback_universallyClosed_surjective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsSeparatedOfIsPullbackUniversallyClosedSurjective.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.isSeparated_of_isPullback_universallyClosed_surjective' : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), UniversallyClosed π → Surjective π → ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π → IsSeparated G'.hom → IsSeparated G.hom := by
  first | exact @GlobalTheory.isSeparated_of_isPullback_universallyClosed_surjective | exact GlobalTheory.isSeparated_of_isPullback_universallyClosed_surjective | (intros; apply GlobalTheory.isSeparated_of_isPullback_universallyClosed_surjective <;> assumption)
