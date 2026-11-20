import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationSeesawStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationInductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationCompatibleLeviStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThKIso

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e he`. Distinguish the cases in `hex : ∃ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s'`. Use `swap`. Conclude with `⟨1, one_ne_zero, fun χX χW om r s r' s' hp => absurd ⟨χX, χW, om, r, s, r', s', hp⟩ hex⟩`. Take `⟨χX₀, χW₀, om₀, r₀, s₀, r₀', s₀', hp₀⟩` from `hex`.

Establish `hB : B.IsGood σ` using `hp₀.base`. Establish `hM : M.IsGood B.ψ` using `hp₀.good`. Establish `hXW : ∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s'` using `⟨_, _, _, _, hp₀.herm, hp₀.skew⟩`. Take `⟨e', he', c, hc, hce⟩` from `GlobalTheory.T.adapted_evaluation_seesaw hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ hB hM hXW e he`. Take `⟨C', hC', hexp⟩` from `GlobalTheory.T.adapted_evaluation_restriction hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he' hB hXW`.

Use `⟨C' * c, mul_ne_zero hC' hc, ?_⟩` and prove the remaining obligations. Introduce `χX χW om r s r' s' hp μ 𝓕 hμ h𝓕 h1 Ψ hΨ ξ hξ hξξ γ hγ hγξ`. Establish `hstd : IsStd B.ψ` using `hp.base.std`. Establish `hspl` using `hp.weil.isUSplitting`. Establish `hpres : ∀ p, ∀ Φ ∈ schA F (Fin n × Fin d), om p Φ ∈ schA F (Fin n × Fin d)` using `fun p Φ hΦ => hspl.pres p Φ hΦ`.

Use `set Ψ' := om (γ, 1) Ψ with hΨ'def`. Establish `hΨ' : Ψ' ∈ schA F (Fin n × Fin d)` using `hpres _ _ hΨ`. Establish `hmove : ∀ u : UA σ W.J, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u) Ψ))) = thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u) Ψ')))`. Introduce `u`. Establish `hu : om (1, u) Ψ ∈ schA F (Fin n × Fin d)` using `hpres _ _ hΨ`.

Establish `hr : M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u) Ψ) ∈ schA F (Fin n × Fin d)` using `GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd _ _ hu`. Rewrite using `[← GlobalTheory.T.adapted_evaluation_equivariant hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ χX χW om r s r' s' hp γ hγ _ hr]`. Use `congr 2`. Rewrite using `[hspl.impl (γ, 1) _ _ hu]`. Establish `hact : actAB (cA σ) ((γ, 1) : UA σ X.J × UA σ W.J) (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) = Matrix.vecMulVec (incV F H.x) (incV F H'.y)`.

Rewrite using `[← hγξ]`. Simplify using `only [actAB]`. Rewrite using `[Matrix.mul_vecMulVec]`. Simplify using `[mat]`. Rewrite using `[hact]`.

Use `congr 1`. Rewrite using `[hΨ'def, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]`. Use `congr 2`. Simplify using the standard rewrite rules. Establish `hφ : ∀ u : UA σ W.J, e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u) Ψ')) ∈ schA F (Fin n × Fin d₁)` using `fun u => he₀.maps _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd _ _ (hpres _ _ hΨ'))`.

Establish `hpt : ∀ u : unip σ W H', thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ))) = C' * ∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) ( …` using `fun u => by`. Rewrite using `[hmove]`. Conclude with `(hexp _ (hφ u.1)).2`. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, GlobalTheory.T.adapted_evaluation_compatible_levi hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he' χX χW om r s r' s' hp μ 𝓕 hμ h𝓕 h1 Ψ' hΨ', tsum_eq_single 0 (fun w hw …`. Establish `hz : Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin d₁ → E)) = 0`.

Use extensionality with `i j`. Simplify using `[incV, Matrix.vecMulVec_apply]`. Establish `hrho0 : ∀ φ : Fn F n d₁, M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin d₁ → E))) φ = φ`. Introduce `φ`. Use function extensionality and compare the values at `x`.

Simplify using `[hz, Darboux.rho, schr]`. Establish `h0 : ∀ u : unip σ W H', thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F 0)) (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u.1) Ψ'))))) = thetaSum F (e' (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ')))`. Introduce `u`. Rewrite using `[hrho0, GlobalTheory.T.adapted_evaluation_nonvanishing hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he' χX χW om r s r' s' hp u.1 u.2 Ψ' hΨ']`. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall h0), integral_const]`.

Establish `hr : M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ' ∈ schA F (Fin n × Fin d)` using `GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd _ _ hΨ'`. Rewrite using `[hce _ hr]`. Establish `hsh : shiftA H H' 1 = Matrix.vecMulVec (incV F H.x) (incV F H'.y)` using `by simp [shiftA]`. Rewrite using `[hsh]`. Simplify using `only [Measure.real, Measure.restrict_apply_univ, h1, ENNReal.toReal_one, one_smul]`.

Simplify using `only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem constTerm_iso : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ →
    ∀ e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁, IsEv B M M₂ H.ι H'.ι (isoA H H') e → ∃ C : ℂ, C ≠ 0 ∧ ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ → μ 𝓕 = 1 →
      ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ ξ : Fin n → E, ξ ≠ 0 → form σ X.J ξ ξ = 0 → ∀ γ ∈ ratU σ X.J, mat γ *ᵥ incV F ξ = incV F H.x →
        ∫ u in 𝓕, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ))) ∂μ = C * thetaSum F (e (M.co.rho B.ψ (shiftA H H' 1) (om (γ, 1) Ψ))) := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e he
  by_cases hex : ∃ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s'
  swap
  · exact ⟨1, one_ne_zero, fun χX χW om r s r' s' hp => absurd ⟨χX, χW, om, r, s, r', s', hp⟩ hex⟩
  obtain ⟨χX₀, χW₀, om₀, r₀, s₀, r₀', s₀', hp₀⟩ := hex
  have hB : B.IsGood σ := hp₀.base
  have hM : M.IsGood B.ψ := hp₀.good
  have hXW : ∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s' := ⟨_, _, _, _, hp₀.herm, hp₀.skew⟩
  obtain ⟨e', he', c, hc, hce⟩ := GlobalTheory.T.adapted_evaluation_seesaw hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ hB hM hXW e he
  obtain ⟨C', hC', hexp⟩ := GlobalTheory.T.adapted_evaluation_restriction hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he' hB hXW
  refine ⟨C' * c, mul_ne_zero hC' hc, ?_⟩
  intro χX χW om r s r' s' hp μ 𝓕 hμ h𝓕 h1 Ψ hΨ ξ hξ hξξ γ hγ hγξ
  have hstd : IsStd B.ψ := hp.base.std
  have hspl := hp.weil.isUSplitting
  have hpres : ∀ p, ∀ Φ ∈ schA F (Fin n × Fin d), om p Φ ∈ schA F (Fin n × Fin d) := fun p Φ hΦ => hspl.pres p Φ hΦ
  set Ψ' := om (γ, 1) Ψ with hΨ'def
  have hΨ' : Ψ' ∈ schA F (Fin n × Fin d) := hpres _ _ hΨ

  have hmove : ∀ u : UA σ W.J, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u) Ψ))) =
      thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u) Ψ'))) := by
    intro u
    have hu : om (1, u) Ψ ∈ schA F (Fin n × Fin d) := hpres _ _ hΨ
    have hr : M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u) Ψ) ∈ schA F (Fin n × Fin d) :=
      GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd _ _ hu
    rw [← GlobalTheory.T.adapted_evaluation_equivariant hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ χX χW om r s r' s' hp γ hγ _ hr]
    congr 2
    rw [hspl.impl (γ, 1) _ _ hu]
    have hact : actAB (cA σ) ((γ, 1) : UA σ X.J × UA σ W.J) (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) =
        Matrix.vecMulVec (incV F H.x) (incV F H'.y) := by
      rw [← hγξ]
      simp only [actAB]
      rw [Matrix.mul_vecMulVec]
      simp [mat]
    rw [hact]
    congr 1
    rw [hΨ'def, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    simp
  have hφ : ∀ u : UA σ W.J, e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u) Ψ')) ∈ schA F (Fin n × Fin d₁) :=
    fun u => he₀.maps _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd _ _ (hpres _ _ hΨ'))
  have hpt : ∀ u : unip σ W H', thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ))) =
      C' * ∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u.1) Ψ'))))) := fun u => by
    rw [hmove]; exact (hexp _ (hφ u.1)).2
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    GlobalTheory.T.adapted_evaluation_compatible_levi hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he' χX χW om r s r' s' hp μ 𝓕 hμ h𝓕 h1 Ψ' hΨ',
    tsum_eq_single 0 (fun w hw => GlobalTheory.T.adapted_evaluation_induction hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he' χX χW om r s r' s' hp μ 𝓕 hμ h𝓕 h1 Ψ' hΨ' w hw)]
  have hz : Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin d₁ → E)) = 0 := by
    ext i j; simp [incV, Matrix.vecMulVec_apply]
  have hrho0 : ∀ φ : Fn F n d₁, M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin d₁ → E))) φ = φ := by
    intro φ; funext x; simp [hz, Darboux.rho, schr]
  have h0 : ∀ u : unip σ W H', thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F 0)) (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u.1) Ψ'))))) = thetaSum F (e' (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ'))) := by
    intro u
    rw [hrho0, GlobalTheory.T.adapted_evaluation_nonvanishing hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he' χX χW om r s r' s' hp u.1 u.2 Ψ' hΨ']
  rw [integral_congr_ae (Filter.Eventually.of_forall h0), integral_const]
  have hr : M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ' ∈ schA F (Fin n × Fin d) :=
    GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd _ _ hΨ'
  rw [hce _ hr]
  have hsh : shiftA H H' 1 = Matrix.vecMulVec (incV F H.x) (incV F H'.y) := by simp [shiftA]
  rw [hsh]
  simp only [Measure.real, Measure.restrict_apply_univ, h1, ENNReal.toReal_one, one_smul]
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]
  ring

end GlobalTheory.ThKIso
