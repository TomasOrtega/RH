import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentClosedFundamentalDomain
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnipotentClosedFundamentalDomain.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.unipotent_closed_fundamental_domain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → IsClosed (unip σ Y H : Set (UA σ Y.J)) ∧ ∀ μN : Measure (unip σ Y H), μN.IsHaarMeasure → ∃ 𝓕 : Set (unip σ Y H), IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μN ∧ μN 𝓕 ≠ 0 ∧ μN 𝓕 ≠ ⊤ := by
  first | exact @GlobalTheory.UnipMassAdapted.closed_and_fundDom | exact GlobalTheory.UnipMassAdapted.closed_and_fundDom | (intros; apply GlobalTheory.UnipMassAdapted.closed_and_fundDom <;> assumption)
