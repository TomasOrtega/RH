import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentralUnipotentTranslate
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCentralUnipotentTranslate.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.exists_central_unipotent_translate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' : ℕ), IsCMExt F E σ → W.IsSkew σ B r' s' →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ t : AF F, ∃ z : UA σ W.J, z ∈ unip σ W H' ∧ (∀ u ∈ unip σ W H', z * u = u * z) ∧
      mat z⁻¹ *ᵥ incV F H'.y = incV F H'.y - algebraMap (AF F) (AE F E) t • incV F H'.x := by
  first | exact @GlobalTheory.UnipMass.CentralShift.exists_central_shift | exact GlobalTheory.UnipMass.CentralShift.exists_central_shift | (intros; apply GlobalTheory.UnipMass.CentralShift.exists_central_shift <;> assumption)
