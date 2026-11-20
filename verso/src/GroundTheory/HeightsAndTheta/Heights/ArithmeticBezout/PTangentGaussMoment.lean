import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsLeadPlaneJac
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsLeadBlockGaussTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

/- English proof (translation)
The claim follows from `(linProjₗ π).map_smul c y`.
-/
theorem linProj_smul_left {m n : ℕ} (π : Fin m → Fin n → ℂ) (c : ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    linProj π (c • y) = c • linProj π y :=
  (linProjₗ π).map_smul c y

/- English proof (translation)
Simplify using `only [Set.indicator, Metric.mem_ball, dist_zero_right, linProj_smul_left, norm_smul, Complex.norm_real, Real.norm_eq_abs, Pi.one_apply]`.
-/
theorem tangentGauss_indicator_eq {m n : ℕ} (π : Fin m → Fin n → ℂ) (r : ℝ) :
    (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec n)) =
      if |r| * ‖linProj π (firstCoordVec n)‖ < 1 then (1 : ℝ≥0∞) else 0 := by
  simp only [Set.indicator, Metric.mem_ball, dist_zero_right, linProj_smul_left, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, Pi.one_apply]

/- English proof (translation)
Unfold `tangentGaussProfile`. Simplify using `only [tangentGauss_indicator_eq, abs_abs]`.
-/
theorem tangentGaussProfile_abs (n m : ℕ) (r : ℝ) :
    tangentGaussProfile n m |r| = tangentGaussProfile n m r := by
  unfold tangentGaussProfile
  simp only [tangentGauss_indicator_eq, abs_abs]

/- English proof (translation)
Introduce `r hr s hs hrs`. Unfold `tangentGaussProfile`. Use `lintegral_mono fun π => ?_` and prove the remaining obligations. Simplify using `only [tangentGauss_indicator_eq, abs_of_nonneg (Set.mem_Ici.1 hr), abs_of_nonneg (Set.mem_Ici.1 hs)]`. Establish `key : s * ‖linProj π (firstCoordVec n)‖ < 1 → r * ‖linProj π (firstCoordVec n)‖ < 1` using `fun h => lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrs (norm_nonneg _)) h`.

Use `gcongr`. Use `split_ifs with h1 h2`. Conclude with `le_rfl`. Conclude with `absurd (key h1) h2`. Conclude with `zero_le_one`.

Conclude with `le_rfl`.
-/
theorem tangentGaussProfile_antitoneOn (n m : ℕ) :
    AntitoneOn (tangentGaussProfile n m) (Set.Ici 0) := by
  intro r hr s hs hrs
  unfold tangentGaussProfile
  refine lintegral_mono fun π => ?_
  simp only [tangentGauss_indicator_eq, abs_of_nonneg (Set.mem_Ici.1 hr),
    abs_of_nonneg (Set.mem_Ici.1 hs)]
  have key : s * ‖linProj π (firstCoordVec n)‖ < 1 → r * ‖linProj π (firstCoordVec n)‖ < 1 :=
    fun h => lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrs (norm_nonneg _)) h
  gcongr
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (key h1) h2
  · exact zero_le_one
  · exact le_rfl

/- English proof (translation)
Establish `hψ : Antitone fun t : ℝ => tangentGaussProfile n m (max t 0)` using `fun a b hab => tangentGaussProfile_antitoneOn n m (Set.mem_Ici.2 (le_max_right a 0)) (Set.mem_Ici.2 (le_max_right b 0)) (max_le_max hab le_rfl)`. Establish `h : tangentGaussProfile n m = fun r => tangentGaussProfile n m (max |r| 0)`. Use function extensionality and compare the values at `r`. Rewrite using `[max_eq_left (abs_nonneg r), tangentGaussProfile_abs]`. Rewrite using `[h]`.

Conclude with `hψ.measurable.comp measurable_abs`.
-/
theorem measurable_tangentGaussProfile (n m : ℕ) : Measurable (tangentGaussProfile n m) := by
  have hψ : Antitone fun t : ℝ => tangentGaussProfile n m (max t 0) := fun a b hab =>
    tangentGaussProfile_antitoneOn n m (Set.mem_Ici.2 (le_max_right a 0))
      (Set.mem_Ici.2 (le_max_right b 0)) (max_le_max hab le_rfl)
  have h : tangentGaussProfile n m = fun r => tangentGaussProfile n m (max |r| 0) := by
    funext r
    rw [max_eq_left (abs_nonneg r), tangentGaussProfile_abs]
  rw [h]
  exact hψ.measurable.comp measurable_abs

/- English proof (translation)
Break down `le_total r 1 with h | h` into its components or cases. Conclude with `(pow_le_one₀ hr h).trans (one_le_pow₀ (by nlinarith))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pow_two_mul_sub_one_le {r : ℝ} (hr : 0 ≤ r) (m : ℕ) : r ^ (2 * m - 1) ≤ (1 + r ^ 2) ^ m := by
  rcases le_total r 1 with h | h
  · exact (pow_le_one₀ hr h).trans (one_le_pow₀ (by nlinarith))
  · calc r ^ (2 * m - 1) ≤ r ^ (2 * m) := pow_le_pow_right₀ h (Nat.sub_le _ _)
      _ = (r ^ 2) ^ m := by rw [pow_mul]
      _ ≤ (1 + r ^ 2) ^ m := pow_le_pow_left₀ (sq_nonneg r) (by linarith) m

/- English proof (translation)
Introduce `n m hm hmn`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Establish `hk : ∀ r : ℝ, tangentGaussProfile (m + k) m r = ∫⁻ π : Fin m → Fin (m + k) → ℂ, matGauss π * (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec (m + k))) * ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2)`. Introduce `r`. Unfold `tangentGaussProfile`.

Simplify using `only [hA m k]`. Establish `hpos : ∀ r : ℝ, 0 < tangentGaussProfile (m + k) m r`. Introduce `r`. Rewrite using `[hk r]`. Establish `hcont : Continuous fun π : Fin m → Fin (m + k) → ℂ => linProj π ((r : ℂ) • firstCoordVec (m + k))`.

Unfold `linProj`. Conclude with `(PiLp.continuous_toLp 2 _).comp (by fun_prop)`. Establish `hdet : Continuous fun π : Fin m → Fin (m + k) → ℂ => (coordPlaneBlock π).det` using `Continuous.matrix_det (by unfold coordPlaneBlock; fun_prop)`. Establish `hmeas : Measurable fun π : Fin m → Fin (m + k) → ℂ => matGauss π * (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec (m + k))) * ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2)`. Use `Measurable.mul (Measurable.mul ?_ ?_) ?_` and prove the remaining obligations.

Unfold `matGauss`. Conclude with `ENNReal.measurable_ofReal.comp (by fun_prop)`. Conclude with `(measurable_one.indicator Metric.isOpen_ball.measurableSet).comp hcont.measurable`. Conclude with `ENNReal.measurable_ofReal.comp ((continuous_norm.comp hdet).pow 2).measurable`. Rewrite using `[lintegral_pos_iff_support hmeas]`.

Use `set U := {π : Fin m → Fin (m + k) → ℂ | linProj π ((r : ℂ) • firstCoordVec (m + k)) ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1}`. Establish `hU : IsOpen U` using `Metric.isOpen_ball.preimage hcont`. Establish `hU0 : (0 : Fin m → Fin (m + k) → ℂ) ∈ U`. Establish `h0 : linProj (0 : Fin m → Fin (m + k) → ℂ) ((r : ℂ) • firstCoordVec (m + k)) = 0`. Use extensionality with `i`.

Simplify using `[linProj]`. Simplify using `only [U, Set.mem_ofPred_eq, h0, Metric.mem_ball, dist_self, zero_lt_one]`. Establish `: (volume : Measure (Fin m → Fin (m + k) → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Use `(hU.measure_pos volume ⟨0, hU0⟩).trans_le (measure_mono_ae ?_)` and prove the remaining obligations. Use `filter_upwards [ae_coordPlaneBlock_det_ne_zero m k] with π hπdet hπU`.

Use `show matGauss π * _ * _ ≠ 0`. Use `mul_ne_zero (mul_ne_zero ?_ ?_) ?_` and prove the remaining obligations. Conclude with `(ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'`. Rewrite using `[Set.indicator_of_mem hπU]`. Conclude with `one_ne_zero`.

Conclude with `(ENNReal.ofReal_pos.2 (by positivity)).ne'`. Take `⟨C, hC⟩` from `hB m k hm`. Establish `hmeasM : Measurable fun r : ℝ => tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))` using `(measurable_tangentGaussProfile _ _).mul (ENNReal.measurable_ofReal.comp (by fun_prop))`. Use `⟨measurable_tangentGaussProfile _ _, tangentGaussProfile_antitoneOn _ _, hpos, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[setLIntegral_pos_iff hmeasM]`.

Establish `hsub : Set.Ioi (0 : ℝ) ⊆ Function.support (fun r : ℝ => tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))) ∩ Set.Ioi 0`. Introduce `r hr`. Use `⟨?_, hr⟩` and prove the remaining obligations. Establish `hm' : (0 : ℝ) < m` using `by exact_mod_cast hm`. Conclude with `mul_ne_zero (hpos r).ne' (ENNReal.ofReal_pos.2 (by`.

Use `Set.mem_Ioi.1 hr` as an intermediate fact. Use the proof step `positivity)).ne'`. Conclude with `lt_of_lt_of_le (by simp) (measure_mono hsub)`. Establish `hle : ∀ r ∈ Set.Ioi (0 : ℝ), tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) ≤ ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹)`. Introduce `r hr`.

Establish `hr0 : 0 ≤ r` using `le_of_lt hr`. Establish `h1` using `pow_two_mul_sub_one_le hr0 m`. Establish `hx : 0 < 1 + r ^ 2` using `by positivity`. Establish `hC0 : 0 ≤ max C 0` using `le_max_right _ _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hk r]`. Use `gcongr`. Conclude with `hC r`. Use `_ = ENNReal.ofReal (C / (1 + r ^ 2) ^ (m + 1) * (2 * m * r ^ (2 * m - 1))) := (ENNReal.ofReal_mul' (by positivity)).symm`. Use `_ ≤ ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) := by`.

Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_max_left _ _`. Use `_ = 2 * m * max C 0 * (1 + r ^ 2)⁻¹ := by`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.
-/
theorem TangentGaussMoment.proof (hA : LeadPlaneJac.Statement) (hB : LeadBlockGaussTail.Statement) :
    TangentGaussMoment.Statement := by
  intro n m hm hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hk : ∀ r : ℝ, tangentGaussProfile (m + k) m r = ∫⁻ π : Fin m → Fin (m + k) → ℂ, matGauss π *
      (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
        (linProj π ((r : ℂ) • firstCoordVec (m + k))) *
      ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2) := by
    intro r
    unfold tangentGaussProfile
    simp only [hA m k]
  have hpos : ∀ r : ℝ, 0 < tangentGaussProfile (m + k) m r := by
    intro r
    rw [hk r]
    have hcont : Continuous fun π : Fin m → Fin (m + k) → ℂ =>
        linProj π ((r : ℂ) • firstCoordVec (m + k)) := by
      unfold linProj
      exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)
    have hdet : Continuous fun π : Fin m → Fin (m + k) → ℂ => (coordPlaneBlock π).det :=
      Continuous.matrix_det (by unfold coordPlaneBlock; fun_prop)
    have hmeas : Measurable fun π : Fin m → Fin (m + k) → ℂ => matGauss π *
        (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
          (linProj π ((r : ℂ) • firstCoordVec (m + k))) *
        ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2) := by
      refine Measurable.mul (Measurable.mul ?_ ?_) ?_
      · unfold matGauss
        exact ENNReal.measurable_ofReal.comp (by fun_prop)
      · exact (measurable_one.indicator Metric.isOpen_ball.measurableSet).comp hcont.measurable
      · exact ENNReal.measurable_ofReal.comp ((continuous_norm.comp hdet).pow 2).measurable
    rw [lintegral_pos_iff_support hmeas]
    set U := {π : Fin m → Fin (m + k) → ℂ |
      linProj π ((r : ℂ) • firstCoordVec (m + k)) ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1}
    have hU : IsOpen U := Metric.isOpen_ball.preimage hcont
    have hU0 : (0 : Fin m → Fin (m + k) → ℂ) ∈ U := by
      have h0 : linProj (0 : Fin m → Fin (m + k) → ℂ) ((r : ℂ) • firstCoordVec (m + k)) = 0 := by
        ext i
        simp [linProj]
      simp only [U, Set.mem_ofPred_eq, h0, Metric.mem_ball, dist_self, zero_lt_one]
    have : (volume : Measure (Fin m → Fin (m + k) → ℂ)).IsAddHaarMeasure :=
      Measure.pi.isAddHaarMeasure _
    refine (hU.measure_pos volume ⟨0, hU0⟩).trans_le (measure_mono_ae ?_)
    filter_upwards [ae_coordPlaneBlock_det_ne_zero m k] with π hπdet hπU
    show matGauss π * _ * _ ≠ 0
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    · rw [Set.indicator_of_mem hπU]
      exact one_ne_zero
    · exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  obtain ⟨C, hC⟩ := hB m k hm
  have hmeasM : Measurable fun r : ℝ =>
      tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) :=
    (measurable_tangentGaussProfile _ _).mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  refine ⟨measurable_tangentGaussProfile _ _, tangentGaussProfile_antitoneOn _ _, hpos, ?_, ?_⟩
  · rw [setLIntegral_pos_iff hmeasM]
    have hsub : Set.Ioi (0 : ℝ) ⊆
        Function.support (fun r : ℝ =>
          tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))) ∩
          Set.Ioi 0 := by
      intro r hr
      refine ⟨?_, hr⟩
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      exact mul_ne_zero (hpos r).ne' (ENNReal.ofReal_pos.2 (by
        have := Set.mem_Ioi.1 hr
        positivity)).ne'
    exact lt_of_lt_of_le (by simp) (measure_mono hsub)
  · have hle : ∀ r ∈ Set.Ioi (0 : ℝ),
        tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) ≤
          ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) := by
      intro r hr
      have hr0 : 0 ≤ r := le_of_lt hr
      have h1 := pow_two_mul_sub_one_le hr0 m
      have hx : 0 < 1 + r ^ 2 := by positivity
      have hC0 : 0 ≤ max C 0 := le_max_right _ _
      calc tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))
          ≤ ENNReal.ofReal (C / (1 + r ^ 2) ^ (m + 1)) * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) := by
            rw [hk r]
            gcongr
            exact hC r
        _ = ENNReal.ofReal (C / (1 + r ^ 2) ^ (m + 1) * (2 * m * r ^ (2 * m - 1))) :=
            (ENNReal.ofReal_mul' (by positivity)).symm
        _ ≤ ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) := by
            refine ENNReal.ofReal_le_ofReal ?_
            calc C / (1 + r ^ 2) ^ (m + 1) * (2 * m * r ^ (2 * m - 1))
                ≤ max C 0 / (1 + r ^ 2) ^ (m + 1) * (2 * m * (1 + r ^ 2) ^ m) := by
                  gcongr
                  exact le_max_left _ _
              _ = 2 * m * max C 0 * (1 + r ^ 2)⁻¹ := by
                  field_simp
                  ring
    calc ∫⁻ r in Set.Ioi (0 : ℝ), tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))
        ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) :=
          setLIntegral_mono' measurableSet_Ioi hle
      _ ≤ ∫⁻ r, ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) := setLIntegral_le_lintegral _ _
      _ < ⊤ := (integrable_inv_one_add_sq.const_mul _).lintegral_lt_top

end

end GroundTheory.Heights₂.Heights
