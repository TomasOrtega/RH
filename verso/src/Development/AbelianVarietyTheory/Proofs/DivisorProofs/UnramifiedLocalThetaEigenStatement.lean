import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedLocalThetaEigen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IndLine.fixed_eq_smul_pVac` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnramifiedLocalThetaEigen.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.unramified_local_theta_eigen : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ (v : Pl F), IsEmpty (E →ₐ[F] Fv F v) → v ∉ X.T → ∀ ξ : Rf.Pi v,
      (∀ k ∈ KAt σ G.W v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, k)) φ φ₁ → Rf.p v φ = ξ → Rf.p v φ₁ = ξ) →
      ∃ c : ℂ, ξ = c • Rf.p v (G.M.vac v) := by
  first | exact @GlobalTheory.IndLine.fixed_eq_smul_pVac | exact GlobalTheory.IndLine.fixed_eq_smul_pVac | (intros; apply GlobalTheory.IndLine.fixed_eq_smul_pVac <;> assumption)
