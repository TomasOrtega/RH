import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyFieldAddEquivGalois
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCohomologyFieldAddEquivGalois.lean&line=235#L235)
-/
theorem _root_.GlobalTheory.T.nonempty_cohomology_addEquiv_galois_cohomology : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (M : Rep.{0} R (Ω ≃ₐ[K] Ω)) [GroundTheory.ProfCoh.IsDiscreteRep M] (e : M ≃+ Sec F (Spec (CommRingCat.of Ω))), (∀ (σ : Ω ≃ₐ[K] Ω) (m : M), e (M.ρ σ m) = Sec.res (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) (e m)) → ∀ n : ℕ, Nonempty (H R (sp K) F n ≃+ GroundTheory.ProfCoh.cohomology M n) := by
  first
  | exact @GlobalTheory.EtC.GalFld.cohomology_field_addEquiv_galois
  | exact GlobalTheory.EtC.GalFld.cohomology_field_addEquiv_galois
  | (intros; apply GlobalTheory.EtC.GalFld.cohomology_field_addEquiv_galois <;> assumption)
