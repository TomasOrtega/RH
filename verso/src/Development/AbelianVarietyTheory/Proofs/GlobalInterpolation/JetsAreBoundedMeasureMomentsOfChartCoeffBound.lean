import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMeasureOfBoundedMoments
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TwistedMeasureMomentsEqShiftedSeriesJets
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

namespace GlobalTheory.MomOneAmice

/- English proof (translation)
Use `set H := hat ι (C ω * logS) G with hH`. Take `⟨μ₁, hμ₁, hsum⟩` from `GlobalTheory.MultiMahler.exists_measure_of_bounded_moments q 1 (fun n => coeff (n 0) H) ⟨1, fun n => hB (n 0)⟩`. Establish `hn1 : ‖μ₁‖ ≤ 1` using `(hμ₁ 1 zero_le_one).2 fun n => hB (n 0)`. Set `e : C(Fin 1 → ℤ_[q], Unit → ℤ_[q])` to `⟨fun a _ => a 0, by fun_prop⟩`. Set `R₀ : C(Unit → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] C(Fin 1 → ℤ_[q], ℂ_[q])` to `{ toFun := fun F => F.comp e map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`.

Establish `hR : ∀ F, ‖R₀ F‖ ≤ 1 * ‖F‖` using `fun F => by`. Rewrite using `[one_mul, ContinuousMap.norm_le _ (norm_nonneg _)]`. Introduce `a`. Conclude with `F.norm_coe_le_norm _`. Set `R` to `R₀.mkContinuous 1 hR`.

Establish `hRn : ‖R‖ ≤ 1` using `LinearMap.mkContinuous_norm_le _ zero_le_one _`. Use `⟨μ₁.comp R, ?_, fun k j f hf => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Take `⟨f₁, hf₁, hs₁⟩` from `GlobalTheory.MomOne.TwistMom.twisted_moments q H 1 0 k ⟨1, hB⟩ (by simp)`. Establish `hF : ∀ a : Fin 1 → ℤ_[q], (R f) a = ∏ i, (fun _ : Fin 1 => f₁) i (a i)` using `fun a => by`.

Express the relevant statement in the definitionally equal form `f (e a) = _`. Rewrite using `[hf, Fin.prod_univ_one, hf₁]`. Simplify using `[e]`. Establish `h2` using `hsum (fun _ => f₁) (R f) hF`. Establish `h3 : HasSum (fun m : ℕ => coeff m H * (fwdDiff (1 : ℤ_[q]))^[m] f₁ 0) (μ₁ (R f))`.

Use `(Equiv.hasSum_iff (Equiv.funUnique (Fin 1) ℕ).symm).2 h2` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `h4` using `h3.unique hs₁`. Rewrite `h4` using `[GlobalTheory.MomOne.Basic.shiftS_one, (GlobalTheory.MomOne.hat_multiplicative_chart q ι ω G (hG.analyticAt 0)).2.1 k]`. Rewrite using `[ContinuousLinearMap.comp_apply, h4, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul, map_mul, map_prod]`.

Simplify using the standard rewrite rules.
-/
theorem momInt_of_bd_hat (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G) (hB : Bd 1 (hat ι (C ω * logS) G)) :
    MomInt ι (fun _ : Unit => ι.symm ω) G := by
  set H := hat ι (C ω * logS) G with hH
  obtain ⟨μ₁, hμ₁, hsum⟩ := GlobalTheory.MultiMahler.exists_measure_of_bounded_moments q 1
    (fun n => coeff (n 0) H) ⟨1, fun n => hB (n 0)⟩
  have hn1 : ‖μ₁‖ ≤ 1 := (hμ₁ 1 zero_le_one).2 fun n => hB (n 0)

  let e : C(Fin 1 → ℤ_[q], Unit → ℤ_[q]) := ⟨fun a _ => a 0, by fun_prop⟩
  let R₀ : C(Unit → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] C(Fin 1 → ℤ_[q], ℂ_[q]) :=
    { toFun := fun F => F.comp e
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hR : ∀ F, ‖R₀ F‖ ≤ 1 * ‖F‖ := fun F => by
    rw [one_mul, ContinuousMap.norm_le _ (norm_nonneg _)]
    intro a
    exact F.norm_coe_le_norm _
  let R := R₀.mkContinuous 1 hR
  have hRn : ‖R‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  refine ⟨μ₁.comp R, ?_, fun k j f hf => ?_⟩
  · calc ‖μ₁.comp R‖ ≤ ‖μ₁‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hn1 hRn (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · obtain ⟨f₁, hf₁, hs₁⟩ := GlobalTheory.MomOne.TwistMom.twisted_moments q H 1 0 k ⟨1, hB⟩ (by simp)
    have hF : ∀ a : Fin 1 → ℤ_[q], (R f) a = ∏ i, (fun _ : Fin 1 => f₁) i (a i) := fun a => by
      change f (e a) = _
      rw [hf, Fin.prod_univ_one, hf₁]
      simp [e]
    have h2 := hsum (fun _ => f₁) (R f) hF
    have h3 : HasSum (fun m : ℕ => coeff m H * (fwdDiff (1 : ℤ_[q]))^[m] f₁ 0) (μ₁ (R f)) := by
      have := (Equiv.hasSum_iff (Equiv.funUnique (Fin 1) ℕ).symm).2 h2
      simpa [Function.comp_def] using this
    have h4 := h3.unique hs₁
    rw [GlobalTheory.MomOne.Basic.shiftS_one, (GlobalTheory.MomOne.hat_multiplicative_chart q ι ω G (hG.analyticAt 0)).2.1 k] at h4
    rw [ContinuousLinearMap.comp_apply, h4, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
      map_mul, map_prod]
    simp

end GlobalTheory.MomOneAmice
