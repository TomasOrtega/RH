import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicThetaAdditive
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThKAnisoAdd.I'_add` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAnisotropicThetaAdditive.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.anisotropic_theta_additive : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.q = 0 →
    ∀ Φ₁ ∈ PolData B G.M', ∀ Φ₂ ∈ PolData B G.M', G.M'.I om' (Φ₁ + Φ₂) = G.M'.I om' Φ₁ + G.M'.I om' Φ₂ := by
  first | exact @GlobalTheory.ThKAnisoAdd.I'_add | exact GlobalTheory.ThKAnisoAdd.I'_add | (intros; apply GlobalTheory.ThKAnisoAdd.I'_add <;> assumption)
