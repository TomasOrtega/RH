import Mathlib
open MeasureTheory
open scoped ComplexOrder

namespace GlobalTheory.SubMeanBall

/- English proof (translation)
Establish `hc : (Circle.exp θ : ℂ) = circleMap 0 1 θ` using `by simp [circleMap, Circle.coe_exp]`. Establish `h1 : MeasurePreserving (fun z : ℂ => circleMap 0 1 θ * z)`. Establish `h` using `(rotation (Circle.exp θ)).measurePreserving`. Establish `e : (⇑(rotation (Circle.exp θ)) : ℂ → ℂ) = fun z => circleMap 0 1 θ * z`. Use function extensionality and compare the values at `z`.

Rewrite using `[rotation_apply, hc]`. Rewrite `h` using `[e]`. Conclude with `h`. Conclude with `volume_preserving_pi (fun _ => h1)`.
-/
theorem measurePreserving_circleMap_smul (g : ℕ) (θ : ℝ) :
    MeasurePreserving (fun w : Fin g → ℂ => circleMap 0 1 θ • w) := by
  have hc : (Circle.exp θ : ℂ) = circleMap 0 1 θ := by simp [circleMap, Circle.coe_exp]
  have h1 : MeasurePreserving (fun z : ℂ => circleMap 0 1 θ * z) := by
    have h := (rotation (Circle.exp θ)).measurePreserving
    have e : (⇑(rotation (Circle.exp θ)) : ℂ → ℂ) = fun z => circleMap 0 1 θ * z := by
      funext z; rw [rotation_apply, hc]
    rw [e] at h
    exact h
  exact volume_preserving_pi (fun _ => h1)

/- English proof (translation)
Rewrite using `[star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_smul]`. Establish `: star c * c = 1`. Rewrite using `[Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]`. Simplify using the standard rewrite rules. Rewrite using `[this, one_smul]`.
-/
theorem herm_smul_of_norm_one {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (hc : ‖c‖ = 1)
    (w : Fin g → ℂ) :
    (c • w) ⬝ᵥ Hm.mulVec (star (c • w)) = w ⬝ᵥ Hm.mulVec (star w) := by
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_smul]
  have : star c * c = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  rw [this, one_smul]

/- English proof (translation)
Use `set h : ℂ → ℂ := fun t => φ (t • w) ^ 2 with hh`. Establish `hd : Differentiable ℂ h`. Introduce `t`. Establish `: DifferentiableAt ℂ (fun t : ℂ => t • w) t` using `(differentiableAt_id.smul_const w)`. Conclude with `((hφ _).comp t this).pow 2`.

Establish `hmv : Real.circleAverage h 0 1 = h 0` using `circleAverage_of_differentiable_on_off_countable (s := ∅) Set.countable_empty hd.continuous.continuousOn (fun z _ => hd z)`. Establish `h0 : h 0 = φ 0 ^ 2` using `by simp [hh]`. Establish `hpi : (0 : ℝ) < 2 * Real.pi` using `by positivity`. Establish `hcont : Continuous fun θ : ℝ => h (circleMap 0 1 θ)` using `hd.continuous.comp (continuous_circleMap 0 1)`. Establish `hle : 2 * Real.pi * ‖φ 0‖ ^ 2 ≤ ∫ θ in Set.Ioc 0 (2 * Real.pi), ‖φ (circleMap 0 1 θ • w)‖ ^ 2`.

Establish `e1 : ‖φ 0‖ ^ 2 = (2 * Real.pi)⁻¹ * ‖∫ θ in (0:ℝ)..2 * Real.pi, h (circleMap 0 1 θ)‖`. Rewrite using `[← norm_pow, ← h0, ← hmv, Real.circleAverage_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpi)]`. Establish `e2 : ‖∫ θ in (0:ℝ)..2 * Real.pi, h (circleMap 0 1 θ)‖ ≤ ∫ θ in (0:ℝ)..2 * Real.pi, ‖h (circleMap 0 1 θ)‖` using `intervalIntegral.norm_integral_le_integral_norm hpi.le`. Establish `e3 : (fun θ : ℝ => ‖h (circleMap 0 1 θ)‖) = fun θ => ‖φ (circleMap 0 1 θ • w)‖ ^ 2`. Use function extensionality and compare the values at `θ`.

Simplify using `[hh, norm_pow]`. Rewrite using `[e1, ← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul]`. Use `e2.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[intervalIntegral.integral_of_le hpi.le, e3]`. Establish `hint : IntegrableOn (fun θ : ℝ => ‖φ (circleMap 0 1 θ • w)‖ ^ 2) (Set.Ioc 0 (2 * Real.pi))`.

Establish `: Continuous fun θ : ℝ => ‖φ (circleMap 0 1 θ • w)‖ ^ 2` using `((hφ.continuous.comp ((continuous_circleMap 0 1).smul continuous_const)).norm).pow 2`. Conclude with `this.integrableOn_Ioc`. Rewrite using `[← ENNReal.ofReal_mul hpi.le, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun θ => by positivity)]`. Conclude with `ENNReal.ofReal_le_ofReal hle`.
-/
theorem circle_bound {g : ℕ} (φ : (Fin g → ℂ) → ℂ) (hφ : Differentiable ℂ φ) (w : Fin g → ℂ) :
    ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (‖φ 0‖ ^ 2) ≤
      ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ENNReal.ofReal (‖φ (circleMap 0 1 θ • w)‖ ^ 2) := by
  set h : ℂ → ℂ := fun t => φ (t • w) ^ 2 with hh
  have hd : Differentiable ℂ h := by
    intro t
    have : DifferentiableAt ℂ (fun t : ℂ => t • w) t :=
      (differentiableAt_id.smul_const w)
    exact ((hφ _).comp t this).pow 2
  have hmv : Real.circleAverage h 0 1 = h 0 :=
    circleAverage_of_differentiable_on_off_countable (s := ∅) Set.countable_empty
      hd.continuous.continuousOn (fun z _ => hd z)
  have h0 : h 0 = φ 0 ^ 2 := by simp [hh]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcont : Continuous fun θ : ℝ => h (circleMap 0 1 θ) :=
    hd.continuous.comp (continuous_circleMap 0 1)
  have hle : 2 * Real.pi * ‖φ 0‖ ^ 2 ≤
      ∫ θ in Set.Ioc 0 (2 * Real.pi), ‖φ (circleMap 0 1 θ • w)‖ ^ 2 := by
    have e1 : ‖φ 0‖ ^ 2 = (2 * Real.pi)⁻¹ * ‖∫ θ in (0:ℝ)..2 * Real.pi, h (circleMap 0 1 θ)‖ := by
      rw [← norm_pow, ← h0, ← hmv, Real.circleAverage_def, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hpi)]
    have e2 : ‖∫ θ in (0:ℝ)..2 * Real.pi, h (circleMap 0 1 θ)‖ ≤
        ∫ θ in (0:ℝ)..2 * Real.pi, ‖h (circleMap 0 1 θ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hpi.le
    have e3 : (fun θ : ℝ => ‖h (circleMap 0 1 θ)‖) = fun θ => ‖φ (circleMap 0 1 θ • w)‖ ^ 2 := by
      funext θ; simp [hh, norm_pow]
    rw [e1, ← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul]
    refine e2.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_of_le hpi.le, e3]
  have hint : IntegrableOn (fun θ : ℝ => ‖φ (circleMap 0 1 θ • w)‖ ^ 2) (Set.Ioc 0 (2 * Real.pi)) := by
    have : Continuous fun θ : ℝ => ‖φ (circleMap 0 1 θ • w)‖ ^ 2 :=
      ((hφ.continuous.comp ((continuous_circleMap 0 1).smul continuous_const)).norm).pow 2
    exact this.integrableOn_Ioc
  rw [← ENNReal.ofReal_mul hpi.le, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun θ => by positivity)]
  exact ENNReal.ofReal_le_ofReal hle

/- English proof (translation)
Introduce `g Hm φ r _ hφ _`. Use `set B := {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2} with hB`. Use `set F : (Fin g → ℂ) → ENNReal := fun w => ENNReal.ofReal (‖φ w‖ ^ 2) with hF`. Establish `hpi : (0:ℝ) < 2 * Real.pi` using `by positivity`. Establish `hinv : ∀ θ : ℝ, ∫⁻ w in B, F (circleMap 0 1 θ • w) = ∫⁻ w in B, F w`.

Introduce `θ`. Establish `hn : ‖circleMap (0:ℂ) 1 θ‖ = 1` using `by simp [norm_circleMap_zero]`. Establish `hc : circleMap (0:ℂ) 1 θ ≠ 0`. Introduce `h0`. Rewrite `hn` using `[h0]`.

Simplify using `at hn`. Establish `hpre : (fun w : Fin g → ℂ => circleMap 0 1 θ • w) ⁻¹' B = B`. Use extensionality with `w`. Simplify using `only [Set.mem_preimage, hB, Set.mem_setOf_eq]`. Rewrite using `[herm_smul_of_norm_one Hm _ hn w]`.

Establish `hemb : MeasurableEmbedding (fun w : Fin g → ℂ => circleMap 0 1 θ • w)` using `(MeasurableEquiv.smul₀ (circleMap 0 1 θ) hc).measurableEmbedding`. Establish `h` using `(measurePreserving_circleMap_smul g θ).setLIntegral_comp_preimage_emb hemb F B`. Rewrite `h` using `[hpre]`. Conclude with `h`. Establish `hmeas : AEMeasurable (Function.uncurry fun (w : Fin g → ℂ) (θ : ℝ) => F (circleMap 0 1 θ • w)) ((volume.restrict B).prod (volume.restrict (Set.Ioc 0 (2 * Real.pi))))`.

Establish `hc : Continuous (Function.uncurry fun (w : Fin g → ℂ) (θ : ℝ) => F (circleMap 0 1 θ • w))` using `ENNReal.continuous_ofReal.comp ((hφ.continuous.comp (((continuous_circleMap 0 1).comp continuous_snd).smul continuous_fst)).norm.pow 2)`. Conclude with `hc.measurable.aemeasurable`. Establish `key : ENNReal.ofReal (2 * Real.pi) * (ENNReal.ofReal (‖φ 0‖ ^ 2) * volume B) ≤ ENNReal.ofReal (2 * Real.pi) * ∫⁻ w in B, F w`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[setLIntegral_const, mul_assoc]`.

Use `_ ≤ ∫⁻ w in B, ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), F (circleMap 0 1 θ • w) := lintegral_mono fun w => circle_bound φ hφ w`. Use `_ = ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ∫⁻ w in B, F (circleMap 0 1 θ • w) := lintegral_lintegral_swap hmeas`. Use `_ = ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ∫⁻ w in B, F w := lintegral_congr fun θ => hinv θ`. Use `_ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ w in B, F w := by`. Rewrite using `[lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc, sub_zero, mul_comm]`.

Conclude with `(ENNReal.mul_le_mul_iff_right (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top).1 key`.
-/
theorem sub_mean_value_ball : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (φ : (Fin g → ℂ) → ℂ) (r : ℝ),
    Hm.PosDef → Differentiable ℂ φ → 0 < r →
    ENNReal.ofReal (‖φ 0‖ ^ 2) * volume {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2} ≤
      ∫⁻ w in {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2}, ENNReal.ofReal (‖φ w‖ ^ 2) := by
  intro g Hm φ r _ hφ _
  set B := {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2} with hB
  set F : (Fin g → ℂ) → ENNReal := fun w => ENNReal.ofReal (‖φ w‖ ^ 2) with hF
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hinv : ∀ θ : ℝ, ∫⁻ w in B, F (circleMap 0 1 θ • w) = ∫⁻ w in B, F w := by
    intro θ
    have hn : ‖circleMap (0:ℂ) 1 θ‖ = 1 := by simp [norm_circleMap_zero]
    have hc : circleMap (0:ℂ) 1 θ ≠ 0 := by
      intro h0; rw [h0] at hn; simp at hn
    have hpre : (fun w : Fin g → ℂ => circleMap 0 1 θ • w) ⁻¹' B = B := by
      ext w; simp only [Set.mem_preimage, hB, Set.mem_setOf_eq]
      rw [herm_smul_of_norm_one Hm _ hn w]
    have hemb : MeasurableEmbedding (fun w : Fin g → ℂ => circleMap 0 1 θ • w) :=
      (MeasurableEquiv.smul₀ (circleMap 0 1 θ) hc).measurableEmbedding
    have h := (measurePreserving_circleMap_smul g θ).setLIntegral_comp_preimage_emb hemb F B
    rw [hpre] at h
    exact h
  have hmeas : AEMeasurable (Function.uncurry fun (w : Fin g → ℂ) (θ : ℝ) => F (circleMap 0 1 θ • w))
      ((volume.restrict B).prod (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
    have hc : Continuous (Function.uncurry fun (w : Fin g → ℂ) (θ : ℝ) => F (circleMap 0 1 θ • w)) :=
      ENNReal.continuous_ofReal.comp ((hφ.continuous.comp
        (((continuous_circleMap 0 1).comp continuous_snd).smul continuous_fst)).norm.pow 2)
    exact hc.measurable.aemeasurable
  have key : ENNReal.ofReal (2 * Real.pi) * (ENNReal.ofReal (‖φ 0‖ ^ 2) * volume B) ≤
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ w in B, F w := by
    calc ENNReal.ofReal (2 * Real.pi) * (ENNReal.ofReal (‖φ 0‖ ^ 2) * volume B)
        = ∫⁻ w in B, ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (‖φ 0‖ ^ 2) := by
          rw [setLIntegral_const, mul_assoc]
      _ ≤ ∫⁻ w in B, ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), F (circleMap 0 1 θ • w) :=
          lintegral_mono fun w => circle_bound φ hφ w
      _ = ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ∫⁻ w in B, F (circleMap 0 1 θ • w) :=
          lintegral_lintegral_swap hmeas
      _ = ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ∫⁻ w in B, F w :=
          lintegral_congr fun θ => hinv θ
      _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ w in B, F w := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
            Real.volume_Ioc, sub_zero, mul_comm]
  exact (ENNReal.mul_le_mul_iff_right (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top).1 key

end GlobalTheory.SubMeanBall
