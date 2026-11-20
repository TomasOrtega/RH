import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

/- English proof (translation)
Introduce `H _ _ _ F`. Establish `hin : ∀ t x y, ⟪F.U t x, F.U t y⟫_ℂ = ⟪x, y⟫_ℂ` using `fun t x y => (⟨(F.U t : H →ₗ[ℂ] H), F.norm t⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y`. Establish `hadj : ∀ t x y, ⟪F.U t x, y⟫_ℂ = ⟪x, F.U (-t) y⟫_ℂ` using `fun t x y => by`. Rewrite using `[← hin t x, ← F.add, add_neg_cancel, F.zero]`. Establish `hw : Integrable wR`.

Use `(integrable_indicator_iff measurableSet_Iic).2 ?_` and prove the remaining obligations. Conclude with `(integrableOn_exp_Iic 0).ofReal`. Establish `spec : ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (F : Flow G) (ψ : ℝ → ℂ), Integrable ψ → ∀ h, Integrable (fun t => ψ t • F.U t h) ∧ F.av ψ h = ∫ t, ψ t • F.U t h`. Introduce `G _ _ _ F ψ hψ`. Establish `hi : ∀ h, Integrable (fun t => ψ t • F.U t h)` using `fun h => hψ.smul_bdd ‖h‖ (F.cont h).aestronglyMeasurable (Eventually.of_forall fun t => (F.norm t h).le)`.

Set `A : G →ₗ[ℂ] G` to `{ toFun := fun h => ∫ t, ψ t • F.U t h map_add' := fun x y => by simp only [map_add, smul_add]; exact integral_add (hi x) (hi y) map_smul' := fun c x => by simp only [map_smul, RingHom.id_apply, smul_comm _ c]; exact integral_smul c _ }`. Establish `hb : ∀ h, ‖A h‖ ≤ (∫ t, ‖ψ t‖) * ‖h‖` using `fun h => by`. Use `(norm_integral_le_integral_norm _).trans_eq ?_` and prove the remaining obligations. Simplify using `only [norm_smul, F.norm]`. Conclude with `integral_mul_const _ _`.

Conclude with `fun h => ⟨hi h, Classical.epsilon_spec (p := fun A : G →L[ℂ] G => ∀ h, A h = ∫ t, ψ t • F.U t h) ⟨A.mkContinuous _ hb, fun _ => rfl⟩ h⟩`. Use `⟨fun t => ?_, hw, ?_, fun ψ hψ => ⟨spec F ψ hψ, ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => by rw [hadj, neg_neg]).symm`. Establish `: (fun t => ‖wR t‖) = (Iic (0 : ℝ)).indicator Real.exp`. Use function extensionality and compare the values at `t`.

Apply the tactic sequence `by_cases h : t ∈ Iic (0 : ℝ) <;> simp [wR, h]`. Rewrite using `[this, integral_indicator measurableSet_Iic, integral_exp_Iic_zero]`. Use `ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _) fun h => ?_` and prove the remaining obligations. Rewrite using `[(spec F ψ hψ h).2]`. Use `(norm_integral_le_integral_norm _).trans_eq ?_` and prove the remaining obligations.

Simplify using `only [norm_smul, F.norm]`. Conclude with `integral_mul_const _ _`. Establish `hψ' : Integrable fun t => conj (ψ (-t))` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hψ.comp_neg`. Use `((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_).symm` and prove the remaining obligations. Rewrite using `[(spec F ψ hψ y).2, (spec F _ hψ' x).2, ← integral_inner (spec F ψ hψ y).1, ← inner_conj_symm, ← integral_inner (spec F _ hψ' x).1, ← integral_conj, ← integral_neg_eq_self]`.

Use `integral_congr_ae (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only [neg_neg, inner_smul_right, map_mul, Complex.conj_conj, inner_conj_symm, hadj]`. Use extensionality with `h`. Rewrite using `[(spec F.rev ψ hψ h).2, (spec F _ hψ.comp_neg h).2, ← integral_neg_eq_self]`. Simplify using `[Flow.rev]`.

Introduce `G _ _ _ F' Y hY`. Use extensionality with `h`. Simplify using `only [ContinuousLinearMap.comp_apply]`. Rewrite using `[(spec F ψ hψ h).2, (spec F' ψ hψ _).2, ← Y.integral_comp_comm (spec F ψ hψ h).1]`. Simplify using `only [map_smul, hY]`.
-/
theorem UpperTheory.V.Z.IntegralApplyAeEq.avSpec :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (F : Flow H), (∀ t, ContinuousLinearMap.adjoint (F.U t) = F.U (-t)) ∧ Integrable wR ∧ (∫ t, ‖wR t‖ = 1) ∧ ∀ ψ : ℝ → ℂ, Integrable ψ →
      (∀ h, Integrable (fun t => ψ t • F.U t h) ∧ F.av ψ h = ∫ t, ψ t • F.U t h) ∧ ‖F.av ψ‖ ≤ ∫ t, ‖ψ t‖ ∧
      ContinuousLinearMap.adjoint (F.av ψ) = F.av (fun t => conj (ψ (-t))) ∧ F.rev.av ψ = F.av (fun t => ψ (-t)) ∧
      ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (F' : Flow G) (Y : H →L[ℂ] G), (∀ t h, Y (F.U t h) = F'.U t (Y h)) → Y ∘L F.av ψ = F'.av ψ ∘L Y := by
  intro H _ _ _ F
  have hin : ∀ t x y, ⟪F.U t x, F.U t y⟫_ℂ = ⟪x, y⟫_ℂ := fun t x y =>
    (⟨(F.U t : H →ₗ[ℂ] H), F.norm t⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y
  have hadj : ∀ t x y, ⟪F.U t x, y⟫_ℂ = ⟪x, F.U (-t) y⟫_ℂ := fun t x y => by
    rw [← hin t x, ← F.add, add_neg_cancel, F.zero]
  have hw : Integrable wR := by
    refine (integrable_indicator_iff measurableSet_Iic).2 ?_
    exact (integrableOn_exp_Iic 0).ofReal
  have spec : ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (F : Flow G) (ψ : ℝ → ℂ), Integrable ψ →
      ∀ h, Integrable (fun t => ψ t • F.U t h) ∧ F.av ψ h = ∫ t, ψ t • F.U t h := by
    intro G _ _ _ F ψ hψ
    have hi : ∀ h, Integrable (fun t => ψ t • F.U t h) := fun h =>
      hψ.smul_bdd ‖h‖ (F.cont h).aestronglyMeasurable (Eventually.of_forall fun t => (F.norm t h).le)
    let A : G →ₗ[ℂ] G :=
      { toFun := fun h => ∫ t, ψ t • F.U t h
        map_add' := fun x y => by simp only [map_add, smul_add]; exact integral_add (hi x) (hi y)
        map_smul' := fun c x => by simp only [map_smul, RingHom.id_apply, smul_comm _ c]; exact integral_smul c _ }
    have hb : ∀ h, ‖A h‖ ≤ (∫ t, ‖ψ t‖) * ‖h‖ := fun h => by
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      simp only [norm_smul, F.norm]
      exact integral_mul_const _ _
    exact fun h => ⟨hi h, Classical.epsilon_spec (p := fun A : G →L[ℂ] G => ∀ h, A h = ∫ t, ψ t • F.U t h)
      ⟨A.mkContinuous _ hb, fun _ => rfl⟩ h⟩
  refine ⟨fun t => ?_, hw, ?_, fun ψ hψ => ⟨spec F ψ hψ, ?_, ?_, ?_, ?_⟩⟩
  · exact ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => by rw [hadj, neg_neg]).symm
  · have : (fun t => ‖wR t‖) = (Iic (0 : ℝ)).indicator Real.exp := by
      funext t
      by_cases h : t ∈ Iic (0 : ℝ) <;> simp [wR, h]
    rw [this, integral_indicator measurableSet_Iic, integral_exp_Iic_zero]
  · refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _) fun h => ?_
    rw [(spec F ψ hψ h).2]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp only [norm_smul, F.norm]
    exact integral_mul_const _ _
  · have hψ' : Integrable fun t => conj (ψ (-t)) := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hψ.comp_neg
    refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_).symm
    rw [(spec F ψ hψ y).2, (spec F _ hψ' x).2, ← integral_inner (spec F ψ hψ y).1, ← inner_conj_symm,
      ← integral_inner (spec F _ hψ' x).1, ← integral_conj, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [neg_neg, inner_smul_right, map_mul, Complex.conj_conj, inner_conj_symm, hadj]
  · ext h
    rw [(spec F.rev ψ hψ h).2, (spec F _ hψ.comp_neg h).2, ← integral_neg_eq_self]
    simp [Flow.rev]
  · intro G _ _ _ F' Y hY
    ext h
    simp only [ContinuousLinearMap.comp_apply]
    rw [(spec F ψ hψ h).2, (spec F' ψ hψ _).2, ← Y.integral_comp_comm (spec F ψ hψ h).1]
    simp only [map_smul, hY]
