import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContinuousLeftInvariantDual.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.continuous_left_invariant_dual : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      Continuous (G.M'.I om' Φ') ∧ ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M'.I om' Φ' (γ * h) = G.M'.I om' Φ' h := by
  first | exact @GlobalTheory.ThKContSmall.contSmall | exact GlobalTheory.ThKContSmall.contSmall | (intros; apply GlobalTheory.ThKContSmall.contSmall <;> assumption)
