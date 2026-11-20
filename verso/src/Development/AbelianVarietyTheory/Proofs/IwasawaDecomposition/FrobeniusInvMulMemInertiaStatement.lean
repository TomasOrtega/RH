import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusInvMulMemInertia
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.frob_inv_mul_mem_inertia` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFrobeniusInvMulMemInertia.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.frobenius_inv_mul_mem_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ τ τ' : G E Ω, IsFrob (F := E) A (normV v) τ →
    IsFrob (F := E) A (normV v) τ' → τ'⁻¹ * τ ∈ Ine (F := E) A := by
  first | exact @GlobalTheory.frob_inv_mul_mem_inertia | exact GlobalTheory.frob_inv_mul_mem_inertia | (intros; apply GlobalTheory.frob_inv_mul_mem_inertia <;> assumption)
