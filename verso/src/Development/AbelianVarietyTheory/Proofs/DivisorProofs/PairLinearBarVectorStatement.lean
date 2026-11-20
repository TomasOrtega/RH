import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairLinearBarVector
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeisMultLin.heis_mult_lin` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPairLinearBarVector.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.pair_linear_bar_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (c : Fin n → AE F E)
    (ι : ((Fin n × Fin d → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F B.v₁) → ℂ)),
    M.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ w : Fin d → Fv F B.v₁, ∃ z : Fin d → AE F E, At (evFin F B.v₁) z ∧
      (∀ l, piW (B.τ₁.comp σ) (z l) = 0) ∧
      ∀ φ ∈ SB (Fin n × Fin d → Fv F B.v₁), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F B.v₁),
        Acts (evFin F B.v₁) (M.co.rho B.ψ (Matrix.vecMulVec c z)) φ φ₁ →
        ∀ Y : Matrix (Fin n) (Fin d) (Fv F B.v₁),
          ι φ₁ Y = psiLoc B.ψ B.v₁ (∑ k, ∑ l, Y k l * piW B.τ₁ (c k) * w l) * ι φ Y := by
  first | exact @GlobalTheory.HeisMultLin.heis_mult_lin | exact GlobalTheory.HeisMultLin.heis_mult_lin | (intros; apply GlobalTheory.HeisMultLin.heis_mult_lin <;> assumption)
