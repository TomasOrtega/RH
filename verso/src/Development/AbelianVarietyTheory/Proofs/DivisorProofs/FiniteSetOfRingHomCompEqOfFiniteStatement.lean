import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetOfRingHomCompEqOfFinite
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteSetOfRingHomCompEqOfFinite.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.finite_setOf_ringHom_comp_eq_of_finite' : ∀ (A Ω K : Type) [CommRing A] [CommRing Ω] [Field K] (φ : A →+* Ω) (ρ : A →+* K), φ.Finite → Set.Finite {τ : Ω →+* K | τ.comp φ = ρ} := by
  first | exact @GlobalTheory.finite_setOf_ringHom_comp_eq_of_finite | exact GlobalTheory.finite_setOf_ringHom_comp_eq_of_finite | (intros; apply GlobalTheory.finite_setOf_ringHom_comp_eq_of_finite <;> assumption)
