import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitBallRayAverageLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeLintegralRayIteratedFDerivStatement
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ _ _ μ _ m hdim`. Use `haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim`. Use `haveI : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ`. Use `set B : Set E := Metric.closedBall (0:E) 1 with hB`. Use `set β : ℝ≥0∞ := μ B with hβ`.

Establish `hβ0 : β ≠ 0` using `(Metric.measure_closedBall_pos μ (0:E) one_pos).ne'`. Establish `hβtop : β ≠ ∞` using `(measure_closedBall_lt_top).ne`. Use `set c : ℝ≥0∞ := ENNReal.ofReal (1 / (m.factorial : ℝ)) * ENNReal.ofReal (1 / ((m : ℝ) + 1)) with hc`. Use `⟨2 * c / β, ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) hβ0, ?_⟩` and prove the remaining obligations. Introduce `F _ _ _ G hG hdec k x`.

Take `⟨φ, hφ1, hφx⟩` from `exists_dual_vector'' ℝ x`. Use `set S : Set E := B ∩ {v | 0 ≤ φ v} with hS`. Establish `hSmeas : MeasurableSet S` using `Metric.isClosed_closedBall.measurableSet.inter (measurableSet_le measurable_const φ.continuous.measurable)`. Establish `hβS : β ≤ 2 * μ S`. Establish `hsub : B ⊆ S ∪ -S`.

Introduce `v hv`. Distinguish the cases in `h : 0 ≤ φ v`. Conclude with `Or.inl ⟨hv, h⟩`. Use `right`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Simplify `hv` using `[hB, Metric.mem_closedBall, norm_neg]`. Use `show 0 ≤ φ (-v)`. Rewrite using `[map_neg]`. Combine the linear relations using `[not_le.mp h]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hDc : Continuous (fun z => ‖iteratedFDeriv ℝ (m + 1) G z‖)` using `(hG.continuous_iteratedFDeriv (by exact_mod_cast (le_top : ((m+1 : ℕ) : ℕ∞) ≤ ⊤))).norm`. Use `set Ψ : E → ℝ≥0∞ := fun y => ENNReal.ofReal (‖x + y‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G (x + y)‖) with hΨ`. Establish `hΨm : Measurable Ψ`. Apply `ENNReal.measurable_ofReal.comp` to reduce the goal to its premises. Conclude with `(((continuous_const.add continuous_id).norm.pow k).mul (hDc.comp (continuous_const.add continuous_id))).measurable`.

Use `set a : ℝ≥0∞ := ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) with ha`. Use `set H : E → ℝ≥0∞ := fun v => ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) with hH`. Establish `hpt : ∀ v ∈ S, v ≠ 0 → a ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v`. Introduce `v hvS hv0`. Establish `hray : ∀ j ≤ m, Tendsto (fun t : ℝ => iteratedFDeriv ℝ j G (x + t • v)) atTop (𝓝 0)`.

Introduce `j hj`. Use `(hdec j hj).comp ?_` and prove the remaining obligations. Rewrite using `[← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]`. Establish `hvpos : 0 < ‖v‖` using `norm_pos_iff.mpr hv0`. Establish `h1 : Tendsto (fun t : ℝ => t * ‖v‖ + -‖x‖) atTop atTop` using `tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const hvpos)`.

Use `tendsto_atTop_mono (fun t => ?_) h1` and prove the remaining obligations. Establish `e1 : ‖t • v‖ ≤ ‖x + t • v‖ + ‖x‖`. Simplify using `using norm_sub_le (x + t • v) x`. Establish `e2 : t * ‖v‖ ≤ ‖t • v‖`. Rewrite using `[norm_smul, Real.norm_eq_abs]`.

Conclude with `mul_le_mul_of_nonneg_right (le_abs_self t) (norm_nonneg v)`. Use `show t * ‖v‖ + -‖x‖ ≤ ‖x + t • v‖`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hR` using `GlobalTheory.T.norm_le_lintegral_ray_iteratedFDeriv' G m x v hG hray`. Establish `hxk : (0:ℝ) ≤ ‖x‖ ^ k` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Use `setLIntegral_mono' measurableSet_Ioi (fun t ht => ?_)` and prove the remaining obligations. Establish `ht0 : (0:ℝ) ≤ t` using `le_of_lt ht`. Establish `hmono : ‖x‖ ≤ ‖x + t • v‖`. Establish `h1 : φ x ≤ φ (x + t • v)`.

Rewrite using `[map_add, map_smul, smul_eq_mul]`. Establish `: 0 ≤ φ v` using `hvS.2`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : φ (x + t • v) ≤ ‖x + t • v‖`. Combine the equalities or inequalities in the displayed calculation.

Establish `h0 : φ x = ‖x‖` using `by simpa using hφx`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpow : ‖x‖ ^ k ≤ ‖x + t • v‖ ^ k` using `pow_le_pow_left₀ (norm_nonneg _) hmono k`. Establish `hfac : (0:ℝ) < m.factorial` using `by exact_mod_cast Nat.factorial_pos m`. Establish `hP : 0 ≤ t ^ m / (m.factorial : ℝ) * (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)` using `by positivity`.

Establish `hA : 0 ≤ t ^ m * ‖v‖ ^ (m + 1)` using `by positivity`. Establish `hf : 0 ≤ 1 / (m.factorial : ℝ)` using `by positivity`. Use `show ENNReal.ofReal (‖x‖ ^ k) * ENNReal.ofReal (t ^ m / (m.factorial : ℝ) * (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * (ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * ENNReal.ofReal (‖x + t • v‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) …`. Rewrite using `[← ENNReal.ofReal_mul hxk, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hf]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Establish `e : 1 / (m.factorial : ℝ) * (t ^ m * ‖v‖ ^ (m + 1) * (‖x + t • v‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) = ‖x + t • v‖ ^ k * (t ^ m / (m.factorial : ℝ) * (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖))` using `by ring`. Rewrite using `[e]`. Conclude with `mul_le_mul_of_nonneg_right hpow hP`. Use `_ = ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`. Establish `hae : ∀ᵐ v ∂(μ.restrict S), a ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v`.

Rewrite using `[ae_restrict_iff' hSmeas]`. Establish `h0 : ∀ᵐ v ∂μ, v ≠ (0:E)`. Rewrite using `[ae_iff]`. Simplify using `[measure_singleton]`. Use `filter_upwards [h0] with v hv0 hvS`.

Conclude with `hpt v hvS hv0`. Establish `hI : ∫⁻ y, Ψ y ∂μ = ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ` using `lintegral_add_left_eq_self (μ := μ) (fun z => ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖)) x`. Establish `hmain : μ S * a ≤ c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ`. Combine the equalities or inequalities in the displayed calculation. Conclude with `inter_subset_left`.

Use `_ ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * (ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ) := by gcongr`. Conclude with `GlobalTheory.T.lintegral_unit_ball_ray_average_le μ Ψ m hΨm hdim`. Use `_ = c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by`. Rewrite using `[hI, hc, mul_assoc]`. Establish `h2 : a * β ≤ 2 * (c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ)`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `(ENNReal.le_div_iff_mul_le (Or.inl hβ0) (Or.inl hβtop)).mpr h2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_eq_mul_inv, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weighted_lintegral_sobolev_pointwise : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (m : ℕ), finrank ℝ E = m + 1 → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : E → F), ContDiff ℝ (⊤ : ℕ∞) G → (∀ j ≤ m, Tendsto (iteratedFDeriv ℝ j G) (cocompact E) (𝓝 0)) → ∀ (k : ℕ) (x : E), ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) ≤ C * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
  intro E _ _ _ _ _ μ _ m hdim
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
  haveI : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  set B : Set E := Metric.closedBall (0:E) 1 with hB
  set β : ℝ≥0∞ := μ B with hβ
  have hβ0 : β ≠ 0 := (Metric.measure_closedBall_pos μ (0:E) one_pos).ne'
  have hβtop : β ≠ ∞ := (measure_closedBall_lt_top).ne
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (m.factorial : ℝ)) * ENNReal.ofReal (1 / ((m : ℝ) + 1)) with hc
  refine ⟨2 * c / β, ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) hβ0, ?_⟩
  intro F _ _ _ G hG hdec k x
  obtain ⟨φ, hφ1, hφx⟩ := exists_dual_vector'' ℝ x
  set S : Set E := B ∩ {v | 0 ≤ φ v} with hS
  have hSmeas : MeasurableSet S :=
    Metric.isClosed_closedBall.measurableSet.inter (measurableSet_le measurable_const φ.continuous.measurable)
  have hβS : β ≤ 2 * μ S := by
    have hsub : B ⊆ S ∪ -S := by
      intro v hv
      by_cases h : 0 ≤ φ v
      · exact Or.inl ⟨hv, h⟩
      · right
        refine ⟨?_, ?_⟩
        · simpa [hB, Metric.mem_closedBall, norm_neg] using hv
        · show 0 ≤ φ (-v)
          rw [map_neg]
          linarith [not_le.mp h]
    calc β ≤ μ (S ∪ -S) := measure_mono hsub
      _ ≤ μ S + μ (-S) := measure_union_le _ _
      _ = 2 * μ S := by rw [Measure.measure_neg, two_mul]
  have hDc : Continuous (fun z => ‖iteratedFDeriv ℝ (m + 1) G z‖) :=
    (hG.continuous_iteratedFDeriv (by exact_mod_cast (le_top : ((m+1 : ℕ) : ℕ∞) ≤ ⊤))).norm
  set Ψ : E → ℝ≥0∞ := fun y => ENNReal.ofReal (‖x + y‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G (x + y)‖) with hΨ
  have hΨm : Measurable Ψ := by
    apply ENNReal.measurable_ofReal.comp
    exact (((continuous_const.add continuous_id).norm.pow k).mul
      (hDc.comp (continuous_const.add continuous_id))).measurable
  set a : ℝ≥0∞ := ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) with ha
  set H : E → ℝ≥0∞ := fun v => ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) with hH
  have hpt : ∀ v ∈ S, v ≠ 0 → a ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v := by
    intro v hvS hv0
    have hray : ∀ j ≤ m, Tendsto (fun t : ℝ => iteratedFDeriv ℝ j G (x + t • v)) atTop (𝓝 0) := by
      intro j hj
      refine (hdec j hj).comp ?_
      rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      have h1 : Tendsto (fun t : ℝ => t * ‖v‖ + -‖x‖) atTop atTop :=
        tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const hvpos)
      refine tendsto_atTop_mono (fun t => ?_) h1
      have e1 : ‖t • v‖ ≤ ‖x + t • v‖ + ‖x‖ := by
        simpa using norm_sub_le (x + t • v) x
      have e2 : t * ‖v‖ ≤ ‖t • v‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (le_abs_self t) (norm_nonneg v)
      show t * ‖v‖ + -‖x‖ ≤ ‖x + t • v‖
      linarith
    have hR := GlobalTheory.T.norm_le_lintegral_ray_iteratedFDeriv' G m x v hG hray
    have hxk : (0:ℝ) ≤ ‖x‖ ^ k := by positivity
    calc a = ENNReal.ofReal (‖x‖ ^ k) * ENNReal.ofReal ‖G x‖ := by rw [ha, ENNReal.ofReal_mul hxk]
      _ ≤ ENNReal.ofReal (‖x‖ ^ k) * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
            (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by gcongr
      _ = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (‖x‖ ^ k) * ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
            (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (m.factorial : ℝ)) *
            (ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v)) := by
          refine setLIntegral_mono' measurableSet_Ioi (fun t ht => ?_)
          have ht0 : (0:ℝ) ≤ t := le_of_lt ht
          have hmono : ‖x‖ ≤ ‖x + t • v‖ := by
            have h1 : φ x ≤ φ (x + t • v) := by
              rw [map_add, map_smul, smul_eq_mul]
              have : 0 ≤ φ v := hvS.2
              nlinarith
            have h2 : φ (x + t • v) ≤ ‖x + t • v‖ := by
              calc φ (x + t • v) ≤ |φ (x + t • v)| := le_abs_self _
                _ = ‖φ (x + t • v)‖ := (Real.norm_eq_abs _).symm
                _ ≤ ‖φ‖ * ‖x + t • v‖ := φ.le_opNorm _
                _ ≤ 1 * ‖x + t • v‖ := mul_le_mul_of_nonneg_right hφ1 (norm_nonneg _)
                _ = ‖x + t • v‖ := one_mul _
            have h0 : φ x = ‖x‖ := by simpa using hφx
            linarith
          have hpow : ‖x‖ ^ k ≤ ‖x + t • v‖ ^ k := pow_le_pow_left₀ (norm_nonneg _) hmono k
          have hfac : (0:ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
          have hP : 0 ≤ t ^ m / (m.factorial : ℝ) *
              (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖) := by positivity
          have hA : 0 ≤ t ^ m * ‖v‖ ^ (m + 1) := by positivity
          have hf : 0 ≤ 1 / (m.factorial : ℝ) := by positivity
          show ENNReal.ofReal (‖x‖ ^ k) * ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
              (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) ≤
            ENNReal.ofReal (1 / (m.factorial : ℝ)) * (ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) *
              ENNReal.ofReal (‖x + t • v‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖))
          rw [← ENNReal.ofReal_mul hxk, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hf]
          apply ENNReal.ofReal_le_ofReal
          have e : 1 / (m.factorial : ℝ) * (t ^ m * ‖v‖ ^ (m + 1) * (‖x + t • v‖ ^ k *
              ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) = ‖x + t • v‖ ^ k * (t ^ m / (m.factorial : ℝ) *
              (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_right hpow hP
      _ = ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hae : ∀ᵐ v ∂(μ.restrict S), a ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v := by
    rw [ae_restrict_iff' hSmeas]
    have h0 : ∀ᵐ v ∂μ, v ≠ (0:E) := by
      rw [ae_iff]
      simp [measure_singleton]
    filter_upwards [h0] with v hv0 hvS
    exact hpt v hvS hv0
  have hI : ∫⁻ y, Ψ y ∂μ = ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ :=
    lintegral_add_left_eq_self (μ := μ) (fun z => ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖)) x
  have hmain : μ S * a ≤ c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
    calc μ S * a = ∫⁻ _ in S, a ∂μ := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ v in S, ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v ∂μ := lintegral_mono_ae hae
      _ = ENNReal.ofReal (1 / (m.factorial : ℝ)) * ∫⁻ v in S, H v ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * ∫⁻ v in B, H v ∂μ := by
          gcongr
          exact inter_subset_left
      _ ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * (ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ) := by
          gcongr
          exact GlobalTheory.T.lintegral_unit_ball_ray_average_le μ Ψ m hΨm hdim
      _ = c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
          rw [hI, hc, mul_assoc]
  have h2 : a * β ≤ 2 * (c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ) := by
    calc a * β ≤ a * (2 * μ S) := by gcongr
      _ = 2 * (μ S * a) := by ring
      _ ≤ _ := by gcongr
  have h3 := (ENNReal.le_div_iff_mul_le (Or.inl hβ0) (Or.inl hβtop)).mpr h2
  calc a ≤ _ := h3
    _ = 2 * c / β * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring

end GlobalTheory
