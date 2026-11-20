import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSqIntegralSmulLe

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.GodementCoeff

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure]
  [ν.IsMulRightInvariant] {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/- English proof (translation)
Establish `hcont : Continuous fun g => ⟪b, ρ g v⟫_ℂ` using `continuous_const.inner (hρ.cont v)`. Establish `hbd : ∀ g, ‖⟪b, ρ g v⟫_ℂ‖ ≤ ‖b‖ * ‖v‖` using `fun g => (norm_inner_le_norm _ _).trans (by rw [hρ.norm])`. Establish `hc2 : IntegrableOn (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) s ν`. Use `Measure.integrableOn_of_bounded (M := (‖b‖ * ‖v‖) ^ 2) hs' (hcont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun g => ?_)` and prove the remaining obligations. Rewrite using `[norm_pow, norm_norm]`.

Conclude with `pow_le_pow_left₀ (norm_nonneg _) (hbd g) 2`. Use `set f : Γ → ℂ := s.indicator (fun g => starRingEnd ℂ ⟪b, ρ g v⟫_ℂ) with hfdef`. Establish `hfm : Measurable f` using `((Complex.continuous_conj.comp hcont).measurable).indicator hs`. Establish `hfi : Integrable f ν`. Use `(integrable_indicator_iff hs).mpr (Measure.integrableOn_of_bounded (M := ‖b‖ * ‖v‖) hs' (Complex.continuous_conj.comp hcont).aestronglyMeasurable (ae_of_all _ fun g => ?_))` and prove the remaining obligations.

Rewrite using `[Complex.norm_conj]`. Conclude with `hbd g`. Establish `hfeq : (fun g => ‖f g‖ ^ 2) = s.indicator (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2)`. Use function extensionality and compare the values at `g`. Apply the tactic sequence `by_cases hg : g ∈ s <;> simp [hfdef, hg, norm_inner_symm]`.

Establish `hf2 : Integrable (fun g => ‖f g‖ ^ 2) ν`. Rewrite using `[hfeq]`. Conclude with `(integrable_indicator_iff hs).mpr hc2`. Establish `hG` using `GlobalTheory.CompanionTheory.Godement.norm_sq_integral_smul_le ν ρ hρ v hm f hfm hfi hf2`. Rewrite `hG` using `[hfeq, integral_indicator hs]`.

Establish `hint : Integrable (fun g => f g • ρ g v) ν` using `hfi.smul_of_top_left (memLp_top_of_bound (hρ.cont v).aestronglyMeasurable ‖v‖ (ae_of_all _ fun g => (hρ.norm g v).le))`. Use `set I := ∫ g in s, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν with hIdef`. Use `set w := ∫ g, f g • ρ g v ∂ν with hwdef`. Establish `hinner : ⟪b, w⟫_ℂ = (I : ℂ)`. Establish `h` using `(innerSL ℂ b).integral_comp_comm hint`.

Simplify using `only [innerSL_apply_apply] at h`. Rewrite using `[hwdef, ← h, hIdef, ← integral_indicator hs, ← integral_complex_ofReal]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : g ∈ s`.

Rewrite using `[hfdef, Set.indicator_of_mem hg, Set.indicator_of_mem hg, inner_smul_right, Complex.conj_mul']`. Use `push_cast`. Both sides reduce to the same expression. Simplify using `[hfdef, hg]`. Establish `hI0 : 0 ≤ I` using `setIntegral_nonneg hs fun _ _ => by positivity`.

Establish `hM0 : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν` using `integral_nonneg fun _ => norm_nonneg _`. Establish `h1 : I ≤ ‖b‖ * ‖w‖`. Establish `h` using `norm_inner_le_norm (𝕜 := ℂ) b w`. Rewrite `h` using `[hinner, Complex.norm_real, Real.norm_of_nonneg hI0]`. Then use the resulting hypothesis. Use `⟨hc2, ?_⟩` and prove the remaining obligations.

Break down `hI0.eq_or_lt with h0 | hpos` into its components or cases. Rewrite using `[← h0]`. Check the signs of the components of the expression. Establish `h2 : I * I ≤ I * ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2)`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `le_of_mul_le_mul_left h2 hpos`.
-/
private theorem integrableOn_and_setIntegral_sq_le_of_isU (ρ : Γ → (B →L[ℂ] B)) (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (b : B) {s : Set Γ} (hs : MeasurableSet s)
    (hs' : ν s ≠ ⊤) :
    IntegrableOn (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) s ν ∧
      ∫ g in s, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  have hcont : Continuous fun g => ⟪b, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  have hbd : ∀ g, ‖⟪b, ρ g v⟫_ℂ‖ ≤ ‖b‖ * ‖v‖ := fun g =>
    (norm_inner_le_norm _ _).trans (by rw [hρ.norm])
  have hc2 : IntegrableOn (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) s ν := by
    refine Measure.integrableOn_of_bounded (M := (‖b‖ * ‖v‖) ^ 2) hs'
      (hcont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd g) 2
  set f : Γ → ℂ := s.indicator (fun g => starRingEnd ℂ ⟪b, ρ g v⟫_ℂ) with hfdef
  have hfm : Measurable f := ((Complex.continuous_conj.comp hcont).measurable).indicator hs
  have hfi : Integrable f ν := by
    refine (integrable_indicator_iff hs).mpr (Measure.integrableOn_of_bounded (M := ‖b‖ * ‖v‖) hs'
      (Complex.continuous_conj.comp hcont).aestronglyMeasurable (ae_of_all _ fun g => ?_))
    rw [Complex.norm_conj]
    exact hbd g
  have hfeq : (fun g => ‖f g‖ ^ 2) = s.indicator (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) := by
    funext g
    by_cases hg : g ∈ s <;> simp [hfdef, hg, norm_inner_symm]
  have hf2 : Integrable (fun g => ‖f g‖ ^ 2) ν := by
    rw [hfeq]
    exact (integrable_indicator_iff hs).mpr hc2
  have hG := GlobalTheory.CompanionTheory.Godement.norm_sq_integral_smul_le ν ρ hρ v hm f hfm hfi hf2
  rw [hfeq, integral_indicator hs] at hG
  have hint : Integrable (fun g => f g • ρ g v) ν :=
    hfi.smul_of_top_left (memLp_top_of_bound (hρ.cont v).aestronglyMeasurable ‖v‖
      (ae_of_all _ fun g => (hρ.norm g v).le))
  set I := ∫ g in s, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν with hIdef
  set w := ∫ g, f g • ρ g v ∂ν with hwdef
  have hinner : ⟪b, w⟫_ℂ = (I : ℂ) := by
    have h := (innerSL ℂ b).integral_comp_comm hint
    simp only [innerSL_apply_apply] at h
    rw [hwdef, ← h, hIdef, ← integral_indicator hs, ← integral_complex_ofReal]
    congr 1
    funext g
    by_cases hg : g ∈ s
    · rw [hfdef, Set.indicator_of_mem hg, Set.indicator_of_mem hg, inner_smul_right,
        Complex.conj_mul']
      push_cast
      rfl
    · simp [hfdef, hg]
  have hI0 : 0 ≤ I := setIntegral_nonneg hs fun _ _ => by positivity
  have hM0 : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  have h1 : I ≤ ‖b‖ * ‖w‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) b w
    rwa [hinner, Complex.norm_real, Real.norm_of_nonneg hI0] at h
  refine ⟨hc2, ?_⟩
  rcases hI0.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · have h2 : I * I ≤ I * ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by
      calc I * I ≤ (‖b‖ * ‖w‖) * (‖b‖ * ‖w‖) := mul_self_le_mul_self hI0 h1
        _ = ‖b‖ ^ 2 * ‖w‖ ^ 2 := by ring
        _ ≤ ‖b‖ ^ 2 * (I * ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) := by gcongr
        _ = I * ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by ring
    exact le_of_mul_le_mul_left h2 hpos

/- English proof (translation)
Establish `hK : 0 ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2` using `mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (sq_nonneg _)`. Establish `hcont : Continuous fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2` using `(continuous_const.inner (hρ.cont v)).norm.pow 2`. Establish `key : ∀ s, MeasurableSet s → ν s ≠ ⊤ → ∫⁻ g in s, ‖‖⟪b, ρ g v⟫_ℂ‖ ^ 2‖ₑ ∂ν ≤ ENNReal.ofReal ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2)`. Introduce `s hs hs'`. Take `⟨hi, hle⟩` from `integrableOn_and_setIntegral_sq_le_of_isU ν ρ hρ v hm b hs hs'`.

Rewrite using `[← ofReal_integral_norm_eq_lintegral_enorm hi]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Simplify `hle` using `only [norm_pow, norm_norm]`. Establish `hInt : Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν` using `integrable_of_forall_fin_meas_le _ ENNReal.ofReal_lt_top hcont.aestronglyMeasurable key`. Use `⟨hInt, ?_⟩` and prove the remaining obligations.

Establish `hle` using `lintegral_le_of_forall_fin_meas_le _ key`. Rewrite `hle` using `[← ofReal_integral_norm_eq_lintegral_enorm hInt, ENNReal.ofReal_le_ofReal_iff hK]`. Simplify `hle` using `only [norm_pow, norm_norm]`.
-/
theorem sq_integrable_and_bound (ρ : Γ → (B →L[ℂ] B)) (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (b : B) :
    Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν ∧
      ∫ g, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  have hK : 0 ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 :=
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (sq_nonneg _)
  have hcont : Continuous fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 :=
    (continuous_const.inner (hρ.cont v)).norm.pow 2
  have key : ∀ s, MeasurableSet s → ν s ≠ ⊤ → ∫⁻ g in s, ‖‖⟪b, ρ g v⟫_ℂ‖ ^ 2‖ₑ ∂ν ≤
      ENNReal.ofReal ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by
    intro s hs hs'
    obtain ⟨hi, hle⟩ := integrableOn_and_setIntegral_sq_le_of_isU ν ρ hρ v hm b hs hs'
    rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
    apply ENNReal.ofReal_le_ofReal
    simpa only [norm_pow, norm_norm] using hle
  have hInt : Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν :=
    integrable_of_forall_fin_meas_le _ ENNReal.ofReal_lt_top hcont.aestronglyMeasurable key
  refine ⟨hInt, ?_⟩
  have hle := lintegral_le_of_forall_fin_meas_le _ key
  rw [← ofReal_integral_norm_eq_lintegral_enorm hInt, ENNReal.ofReal_le_ofReal_iff hK] at hle
  simpa only [norm_pow, norm_norm] using hle

end GlobalTheory.CompanionTheory.GodementCoeff

end
