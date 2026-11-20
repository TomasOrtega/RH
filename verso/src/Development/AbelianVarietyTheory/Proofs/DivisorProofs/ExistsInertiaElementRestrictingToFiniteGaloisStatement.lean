import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertiaElementRestrictingToFiniteGalois
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertiaRestrict.exists_mem_inertia_eq_on` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsInertiaElementRestrictingToFiniteGalois.lean&line=150#L150)
-/
theorem _root_.GlobalTheory.T.exists_inertia_element_restricting_to_finite_galois : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] (τ : L ≃ₐ[K] L), τ ∈ inertia K (V.comap (algebraMap L Ω)) → ∃ σ ∈ inertia K V, ∀ y : L, σ (y : Ω) = (τ y : Ω) := by
  first | exact @GlobalTheory.InertiaRestrict.exists_mem_inertia_eq_on | exact GlobalTheory.InertiaRestrict.exists_mem_inertia_eq_on | (intros; apply GlobalTheory.InertiaRestrict.exists_mem_inertia_eq_on <;> assumption)
