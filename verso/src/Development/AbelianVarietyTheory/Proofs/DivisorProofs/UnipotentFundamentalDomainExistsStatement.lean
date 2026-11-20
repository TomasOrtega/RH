import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomainExists
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnipotentFundamentalDomainExists.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.unipotent_fundamental_domain_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ μN : Measure (unip σ G.V H), μN.IsHaarMeasure →
    ∃ 𝓕 : Set (unip σ G.V H), IsFundamentalDomain ((ratU σ G.V.J).subgroupOf (unip σ G.V H)) 𝓕 μN ∧ μN 𝓕 ≠ 0 ∧ μN 𝓕 ≠ ⊤ := by
  first | exact @GlobalTheory.UnipMassHerm.exists_fundDom_unip_herm | exact GlobalTheory.UnipMassHerm.exists_fundDom_unip_herm | (intros; apply GlobalTheory.UnipMassHerm.exists_fundDom_unip_herm <;> assumption)
