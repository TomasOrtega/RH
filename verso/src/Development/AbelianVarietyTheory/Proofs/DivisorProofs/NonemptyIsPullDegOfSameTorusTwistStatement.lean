import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegOfSameTorusTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonemptyIsPullDegOfSameTorusTwist.lean&line=154#L154)
-/
theorem _root_.GlobalTheory.T.nonempty_isPullDeg_of_same_torus_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D₂ D : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g → Nonempty (IsPullDeg (RingHom.id R) D₀.toPre D₂.toPre) := by
  first | exact @GlobalTheory.MumCmp.Uniq.nonempty_isPullDeg_of_isTwist | exact GlobalTheory.MumCmp.Uniq.nonempty_isPullDeg_of_isTwist | (intros; apply GlobalTheory.MumCmp.Uniq.nonempty_isPullDeg_of_isTwist <;> assumption)
