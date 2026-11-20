import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMovesYByIotaAndX
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnipotentMovesYByIotaAndX.lean&line=111#L111)
-/
theorem _root_.GlobalTheory.T.unipotent_moves_y_by_iota_and_x : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' : ℕ), IsCMExt F E σ → W.IsSkew σ B r' s' →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ u ∈ unip σ W H', ∃ (z : Fin d₁ → AE F E) (β : AE F E),
      mat u *ᵥ incV F H'.y = incV F H'.y + incM F H'.ι *ᵥ z + β • incV F H'.x := by
  first | exact @GlobalTheory.IsoMove.unip_mulVec_y | exact GlobalTheory.IsoMove.unip_mulVec_y | (intros; apply GlobalTheory.IsoMove.unip_mulVec_y <;> assumption)
