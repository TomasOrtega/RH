import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentQuotientUnitVolume
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThK.UnipDomPlane.exists_haar_fundamentalDomain_one_plane` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnipotentQuotientUnitVolume.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.unipotent_quotient_unit_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (Y.J j i) = -Y.J i j) → IsIsoPlane σ B H Y Y₁ →
      ∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1 := by
  first | exact @GlobalTheory.ThK.UnipDomPlane.exists_haar_fundamentalDomain_one_plane | exact GlobalTheory.ThK.UnipDomPlane.exists_haar_fundamentalDomain_one_plane | (intros; apply GlobalTheory.ThK.UnipDomPlane.exists_haar_fundamentalDomain_one_plane <;> assumption)
