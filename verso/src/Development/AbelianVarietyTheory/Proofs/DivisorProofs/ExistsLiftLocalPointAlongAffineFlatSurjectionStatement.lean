import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftLocalPointAlongAffineFlatSurjection
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LiftLocal.lift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLiftLocalPointAlongAffineFlatSurjection.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.exists_lift_localPoint_along_affine_flat_surjection : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Scheme.{0}) (π : Y ⟶ X) [IsAffineHom π] [Flat π] [Surjective π] (x : Sp R ⟶ X), ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (φ : R →+* R'), IsLocalHom φ ∧ Function.Injective φ ∧ ∃ x' : Sp R' ⟶ Y, x' ≫ π = spMap φ ≫ x := by
  first | exact @GlobalTheory.LiftLocal.lift | exact GlobalTheory.LiftLocal.lift | (intros; apply GlobalTheory.LiftLocal.lift <;> assumption)
