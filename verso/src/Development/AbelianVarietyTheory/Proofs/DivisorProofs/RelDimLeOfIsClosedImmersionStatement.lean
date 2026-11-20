import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimLeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelDimLeOfIsClosedImmersion.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.relDim_le_of_smooth_of_isClosedImmersion : ∀ (k : Type) [Field k] (N G : Over (Sp k)) (ν : N ⟶ G), IsClosedImmersion ν.left → Nonempty N.left → ∀ g g' : ℕ, SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g' N.hom → g' ≤ g := by
  first | exact @GlobalTheory.relDim_le_of_isClosedImmersion | exact GlobalTheory.relDim_le_of_isClosedImmersion | (intros; apply GlobalTheory.relDim_le_of_isClosedImmersion <;> assumption)
