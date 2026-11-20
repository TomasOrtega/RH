import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherian
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FRegAtNoetherianModelNoetherian.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.regAt_noetherian_model_noetherian : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω), CoordTie o ξ x → (∀ p : Cpt ξ, IsNoetherianRing (regAt ξ p)) ∧ ((∀ q : X, genPt ξ ⤳ q) → IsNoetherian X ∧ IsIntegral X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie | exact GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie <;> assumption)
