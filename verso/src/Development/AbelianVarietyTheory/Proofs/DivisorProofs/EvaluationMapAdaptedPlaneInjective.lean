import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneEquivariantStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKExpandLin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]`.
-/
theorem rho_add (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E)) (Φ Ψ : Fn F n d) :
    M.co.rho ψ u (Φ + Ψ) = M.co.rho ψ u Φ + M.co.rho ψ u Ψ := by
  funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rho_smul (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E)) (c : ℂ) (Φ : Fn F n d) :
    M.co.rho ψ u (c • Φ) = c • M.co.rho ψ u Φ := by
  funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]; ring

/- English proof (translation)
Use `⟨fun Ψ hΨ Ψ' hΨ' => ?_, fun c Ψ => ?_⟩` and prove the remaining obligations. Establish `h : ∀ ξ, thetaSum F (e₀ (M.co.rho ψ (u ξ) (Ψ + Ψ'))) = thetaSum F (e₀ (M.co.rho ψ (u ξ) Ψ)) + thetaSum F (e₀ (M.co.rho ψ (u ξ) Ψ'))` using `fun ξ => by`. Rewrite using `[rho_add, map_add]`. Conclude with `GlobalTheory.WeilM.thetaSum_add F (he _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ Ψ hΨ)) (he _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ Ψ' hΨ'))`. Rewrite using `[tsum_congr h]`.

Conclude with `(hs Ψ hΨ).tsum_add (hs Ψ' hΨ')`. Establish `h : ∀ ξ, thetaSum F (e₀ (M.co.rho ψ (u ξ) (c • Ψ))) = c * thetaSum F (e₀ (M.co.rho ψ (u ξ) Ψ))` using `fun ξ => by`. Rewrite using `[rho_smul, map_smul]`. Conclude with `GlobalTheory.WeilM.thetaSum_smul F c _`. Rewrite using `[tsum_congr h, tsum_mul_left]`.
-/
theorem lin_of_summable {ι : Type} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁) (he : ∀ Φ ∈ schA F (Fin n × Fin d), e₀ Φ ∈ schA F (Fin n × Fin d₁))
    (u : ι → Matrix (Fin n) (Fin d) (AE F E))
    (hs : ∀ Ψ ∈ schA F (Fin n × Fin d), Summable fun ξ => thetaSum F (e₀ (M.co.rho ψ (u ξ) Ψ))) :
    (∀ Ψ ∈ schA F (Fin n × Fin d), ∀ Ψ' ∈ schA F (Fin n × Fin d),
      (∑' ξ, thetaSum F (e₀ (M.co.rho ψ (u ξ) (Ψ + Ψ')))) =
        (∑' ξ, thetaSum F (e₀ (M.co.rho ψ (u ξ) Ψ))) + ∑' ξ, thetaSum F (e₀ (M.co.rho ψ (u ξ) Ψ'))) ∧
    ∀ c : ℂ, ∀ Ψ : Fn F n d,
      (∑' ξ, thetaSum F (e₀ (M.co.rho ψ (u ξ) (c • Ψ)))) = c * ∑' ξ, thetaSum F (e₀ (M.co.rho ψ (u ξ) Ψ)) := by
  refine ⟨fun Ψ hΨ Ψ' hΨ' => ?_, fun c Ψ => ?_⟩
  · have h : ∀ ξ, thetaSum F (e₀ (M.co.rho ψ (u ξ) (Ψ + Ψ'))) =
        thetaSum F (e₀ (M.co.rho ψ (u ξ) Ψ)) + thetaSum F (e₀ (M.co.rho ψ (u ξ) Ψ')) := fun ξ => by
      rw [rho_add, map_add]
      exact GlobalTheory.WeilM.thetaSum_add F (he _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ Ψ hΨ))
        (he _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ Ψ' hΨ'))
    rw [tsum_congr h]
    exact (hs Ψ hΨ).tsum_add (hs Ψ' hΨ')
  · have h : ∀ ξ, thetaSum F (e₀ (M.co.rho ψ (u ξ) (c • Ψ))) = c * thetaSum F (e₀ (M.co.rho ψ (u ξ) Ψ)) := fun ξ => by
      rw [rho_smul, map_smul]
      exact GlobalTheory.WeilM.thetaSum_smul F c _
    rw [tsum_congr h, tsum_mul_left]

end GlobalTheory.ThKExpandLin

namespace GlobalTheory.ThKExpandLin

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he hB hM hXW`. Take `⟨h1, h2⟩` from `lin_of_summable M B.ψ hB.std e₀ he.maps _ (hsumm hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he hB hM hXW)`. Conclude with `⟨h1, fun c Ψ _ => h2 c Ψ⟩`.
-/
theorem main_of_summ (hsumm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∀ Ψ ∈ schA F (Fin n × Fin d), Summable (fun ξ : Fin n → E => thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ)))) :
    GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    (∀ Ψ ∈ schA F (Fin n × Fin d), ∀ Ψ' ∈ schA F (Fin n × Fin d), (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (Ψ + Ψ')))) = (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (Ψ)))) + (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (Ψ'))))) ∧
      ∀ c : ℂ, ∀ Ψ ∈ schA F (Fin n × Fin d), (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (c • Ψ)))) = c * (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (Ψ)))) := by
  intro hK F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he hB hM hXW
  obtain ⟨h1, h2⟩ := lin_of_summable M B.ψ hB.std e₀ he.maps _
    (hsumm hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he hB hM hXW)
  exact ⟨h1, fun c Ψ _ => h2 c Ψ⟩

end GlobalTheory.ThKExpandLin

namespace GlobalTheory.ThKExpandLin

/- English proof (translation)
The claim follows from `main_of_summ GlobalTheory.T.evaluation_map_adapted_plane_equivariant`.
-/
theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    (∀ Ψ ∈ schA F (Fin n × Fin d), ∀ Ψ' ∈ schA F (Fin n × Fin d), (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (Ψ + Ψ')))) = (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (Ψ)))) + (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (Ψ'))))) ∧
      ∀ c : ℂ, ∀ Ψ ∈ schA F (Fin n × Fin d), (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (c • Ψ)))) = c * (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (Ψ)))) :=
  main_of_summ GlobalTheory.T.evaluation_map_adapted_plane_equivariant

end GlobalTheory.ThKExpandLin
