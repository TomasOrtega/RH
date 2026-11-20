import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAbelianizedGaloisHomOfClosureIso
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsAbelianizedGaloisHomOfClosureIso.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.exists_abelianizedGalois_hom_of_closureIso : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (φ : Ω ≃+* Ω') (j : E →+* E'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → ∃ ρ : GlobalTheory.HeckeGal.Gab E' Ω' →* GlobalTheory.HeckeGal.Gab E Ω, Continuous ρ ∧ ∀ (τ : Formalism.ConjugateSelfDual.G E' Ω') (σ : Formalism.ConjugateSelfDual.G E Ω), (∀ z, φ (σ z) = τ (φ z)) → ρ (GlobalTheory.HeckeGal.toAb E' Ω' τ) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  first | exact @GlobalTheory.HeckeGal.exists_abHom_of_ringEquiv | exact GlobalTheory.HeckeGal.exists_abHom_of_ringEquiv | (intros; apply GlobalTheory.HeckeGal.exists_abHom_of_ringEquiv <;> assumption)
