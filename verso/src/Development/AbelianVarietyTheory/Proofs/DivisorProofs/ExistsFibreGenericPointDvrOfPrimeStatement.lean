import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreGenericPointDvrOfPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.VerticalUnit.exists_fibre_generic_of_prime` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFibreGenericPointDvrOfPrime.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_fibre_genericPoint_dvr_of_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (π : R), Prime π → ∃ ξ : X, (q ξ).asIdeal = Ideal.span {π} ∧ (∀ x : X, (q x).asIdeal = Ideal.span {π} → ξ ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk ξ) ∧ Irreducible (X.presheaf.germ ⊤ ξ trivial (constFn q ⊤ π)) := by
  first | exact @GlobalTheory.VerticalUnit.exists_fibre_generic_of_prime | exact GlobalTheory.VerticalUnit.exists_fibre_generic_of_prime | (intros; apply GlobalTheory.VerticalUnit.exists_fibre_generic_of_prime <;> assumption)
