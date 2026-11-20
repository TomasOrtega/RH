import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairAnisotropicThetaFinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThK.DiffCont.continuous_diff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMatchedPairAnisotropicThetaFinite.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.matched_pair_anisotropic_theta_finite : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ c : ℂ, ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
    ∀ c₀ : E, c₀ ≠ 0 → ∀ φ' : GAd σ (c₀ • G.W.J.map σ) → ℂ,
      (∀ (g : UA σ G.W.J) (g' : GAd σ (c₀ • G.W.J.map σ)), g.1 = g'.1 → φ' g' = G.M.I om Φ g - c * G.M'.I om' Φ' g) →
      Continuous φ' := by
  first | exact @GlobalTheory.ThK.DiffCont.continuous_diff | exact GlobalTheory.ThK.DiffCont.continuous_diff | (intros; apply GlobalTheory.ThK.DiffCont.continuous_diff <;> assumption)
