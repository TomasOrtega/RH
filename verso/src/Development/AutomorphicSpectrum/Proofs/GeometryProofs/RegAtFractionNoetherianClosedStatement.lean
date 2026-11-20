import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FRegAtFractionNoetherianClosed.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.regAt_fraction_noetherian_closed : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω ∧ (IsNoetherianRing (X.presheaf.stalk p.1) → IsNoetherianRing (regAt ξ p)) ∧ (IsIntegrallyClosed (X.presheaf.stalk p.1) → IsIntegrallyClosed (regAt ξ p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring | exact GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring | (intros; apply GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring <;> assumption)
