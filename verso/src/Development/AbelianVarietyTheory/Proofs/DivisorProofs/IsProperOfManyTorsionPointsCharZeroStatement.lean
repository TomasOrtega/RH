import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfManyTorsionPointsCharZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ManyTorsionProper.isProper_of_many_torsion_charZero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsProperOfManyTorsionPointsCharZero.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.isProper_of_many_torsion_points_charZero : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  first | exact @GlobalTheory.ManyTorsionProper.isProper_of_many_torsion_charZero | exact GlobalTheory.ManyTorsionProper.isProper_of_many_torsion_charZero | (intros; apply GlobalTheory.ManyTorsionProper.isProper_of_many_torsion_charZero <;> assumption)
