import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def pairF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (x : Mt k r) : ℂ :=
  herm (Hpk k r) (Matrix.of x *ᵥ z') z

def pairConst (k : ℕ) (T T' : ℝ) : ℝ := 2 * volU k ^ 2 / ((T * T') ^ k * volU (k - 1))

def RhsTest : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ g : ℂ → ℝ≥0∞, Measurable g →
      rhsW k r z z' μW μW' μsec (fun x => g (pairF k r z z' x)) =
        ENNReal.ofReal (a * a') * ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * g ζ

def PairPush : Prop :=
  ∀ (k r : ℕ) (νg : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) νg →
    ∀ z z' : Fin (2 * r + k + 1) → ℂ, inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ g : ℂ → ℝ≥0∞, Measurable g →
      ∫⁻ x, g (pairF k r z z' x) ∂νg = ENNReal.ofReal (pairConst k (Tz k r z) (Tz k r z')) *
        ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * g ζ

def rmulM {k r : ℕ} (p : Mat k r) (x : Mt k r) : Mt k r := Matrix.of x * p

def TransW : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ p ∈ UWb k r, p *ᵥ ((Real.sqrt (Tz k r z) : ℂ) • wLast k r) = z

def UnimodW : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) ν →
    ∀ p ∈ UWb k r, ν.map (rmulM p) = ν

def OrbitPushG : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z' → 0 < Tz k r z' →
    ∀ νg : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    ∀ f : (Fin k → ℂ) × ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ x, f (fun i => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i)),
          (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) ∂νg =
        ENNReal.ofReal (volU k * 2 ^ (k + 1) / Tz k r z' ^ k) * hypMeas k (Tz k r z') f

/- English proof (translation)
The claim follows from `Finset.prod_pos fun i _ => by positivity`.
-/
theorem volU_pos (j : ℕ) : 0 < volU j :=
  Finset.prod_pos fun i _ => by positivity

/- English proof (translation)
Unfold `pairF herm`. Conclude with `continuous_const.dotProduct (continuous_const.matrix_mulVec ((show Continuous fun x : Mt k r => Matrix.of x from continuous_id).matrix_mulVec continuous_const))`.
-/
theorem continuous_pairF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (pairF k r z z') := by
  unfold pairF herm
  exact continuous_const.dotProduct (continuous_const.matrix_mulVec
    ((show Continuous fun x : Mt k r => Matrix.of x from continuous_id).matrix_mulVec continuous_const))

/- English proof (translation)
Use `⟨hH, ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : Mat k r) ∈ UWb k r`. Apply the tactic sequence `refine ⟨?_, fun a => ⟨?_, ?_⟩⟩ <;> simp [UH]`. Establish `e : ∀ ρ, tBall k r 1 ρ = expBall (k` using `k) (r := r) (UWb k r) ρ := fun ρ => by`. Use extensionality with `x`.

Simplify using `[tBall, bBall]`. Establish `h2` using `hL 1 h1`. Simplify using `only [e] at h2`. Conclude with `h2`.
-/
theorem gauge_of_lim {k r : ℕ} (νg : Measure (Mt k r)) (hH : IsHaarOn (UWb k r) νg)
    (hL : ∀ m ∈ UWb k r, Tendsto (fun ρ : ℝ => (νg (tBall k r m ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1)) :
    IsGaugeOn k r (UWb k r) νg := by
  refine ⟨hH, ?_⟩
  have h1 : (1 : Mat k r) ∈ UWb k r := by
    refine ⟨?_, fun a => ⟨?_, ?_⟩⟩ <;> simp [UH]
  have e : ∀ ρ, tBall k r 1 ρ = expBall (k := k) (r := r) (UWb k r) ρ := fun ρ => by
    ext x
    simp [tBall, bBall]
  have h2 := hL 1 h1
  simp only [e] at h2
  exact h2

def annU (T T' : ℝ) : Set ℂ := {ζ | T * T' < Complex.normSq ζ ∧ Complex.normSq ζ < 4 * (T * T')}

/- English proof (translation)
The claim follows from `(isOpen_lt continuous_const Complex.continuous_normSq).inter (isOpen_lt Complex.continuous_normSq continuous_const)`.
-/
theorem annU_open (T T' : ℝ) : IsOpen (annU T T') :=
  (isOpen_lt continuous_const Complex.continuous_normSq).inter
    (isOpen_lt Complex.continuous_normSq continuous_const)

/- English proof (translation)
Establish `hAo : IsOpen (annU T T')` using `annU_open T T'`. Prove the components needed by the constructor for the conclusion. Establish `hVo : IsOpen {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}` using `(isOpen_lt continuous_const Complex.continuous_normSq).inter (isOpen_lt Complex.continuous_normSq continuous_const)`. Establish `hVne : {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.Nonempty`. Apply the tactic sequence `refine ⟨((Real.sqrt (5 / 2 * (T * T')) : ℝ) : ℂ), ?_, ?_⟩ <;>`.

Apply the tactic sequence `rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)] <;> linarith`. Establish `hVpos` using `hVo.measure_pos volume hVne`. Establish `hle : ∀ ζ, ENNReal.ofReal ((T * T') ^ (k - 1)) * {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.indicator 1 ζ ≤ ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ`. Introduce `ζ`. Distinguish the cases in `hζ : 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')`.

Establish `hU : ζ ∈ annU T T'` using `⟨by linarith [hζ.1], by linarith [hζ.2]⟩`. Establish `hV : ζ ∈ {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}` using `hζ`. Rewrite using `[Set.indicator_of_mem hV, Set.indicator_of_mem hU, Pi.one_apply, mul_one, mul_one]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Unfold `zWeight`.

Rewrite using `[if_pos (by linarith [hζ.1])]`. Conclude with `pow_le_pow_left₀ hTT.le (by linarith [hζ.1]) _`. Establish `hV : ζ ∉ {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}` using `hζ`. Simplify using `[Set.indicator_apply, hV]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[lintegral_const_mul _ (measurable_one.indicator hVo.measurableSet), lintegral_indicator_one hVo.measurableSet]`. Use `_ ≤ _ := lintegral_mono hle`. Establish `hM : ∀ ζ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ ≤ ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * (annU T T').indicator 1 ζ`. Introduce `ζ`. Distinguish the cases in `hζ : ζ ∈ annU T T'`.

Rewrite using `[Set.indicator_of_mem hζ, Pi.one_apply, mul_one, mul_one]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Unfold `zWeight`. Rewrite using `[if_pos hζ.1.le]`. Conclude with `pow_le_pow_left₀ (by linarith [hζ.1]) (by linarith [hζ.2]) _`.

Simplify using `[Set.indicator_apply, hζ]`. Establish `hsub : annU T T' ⊆ Metric.ball 0 (2 * Real.sqrt (T * T') + 1)`. Introduce `ζ hζ`. Rewrite using `[Metric.mem_ball, dist_zero_right]`. Establish `h1 : ‖ζ‖ ^ 2 < (2 * Real.sqrt (T * T')) ^ 2`.

Rewrite using `[← Complex.normSq_eq_norm_sq, mul_pow, Real.sq_sqrt hTT.le]`. Combine the linear relations using `[hζ.2]`. Establish `h2` using `lt_of_pow_lt_pow_left₀ 2 (by positivity) h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfin : volume (annU T T') < ⊤` using `(measure_mono hsub).trans_lt measure_ball_lt_top`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_const_mul _ (measurable_one.indicator hAo.measurableSet), lintegral_indicator_one hAo.measurableSet]`. Use `_ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin`.
-/
theorem testJ (k : ℕ) (T T' : ℝ) (hTT : 0 < T * T') :
    0 < ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ ∧
      ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ < ⊤ := by
  have hAo : IsOpen (annU T T') := annU_open T T'
  constructor
  ·
    have hVo : IsOpen {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} :=
      (isOpen_lt continuous_const Complex.continuous_normSq).inter
        (isOpen_lt Complex.continuous_normSq continuous_const)
    have hVne : {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.Nonempty := by
      refine ⟨((Real.sqrt (5 / 2 * (T * T')) : ℝ) : ℂ), ?_, ?_⟩ <;>
        rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)] <;> linarith
    have hVpos := hVo.measure_pos volume hVne
    have hle : ∀ ζ, ENNReal.ofReal ((T * T') ^ (k - 1)) *
        {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.indicator 1 ζ ≤
        ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ := by
      intro ζ
      by_cases hζ : 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')
      · have hU : ζ ∈ annU T T' := ⟨by linarith [hζ.1], by linarith [hζ.2]⟩
        have hV : ζ ∈ {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} := hζ
        rw [Set.indicator_of_mem hV, Set.indicator_of_mem hU, Pi.one_apply, mul_one, mul_one]
        apply ENNReal.ofReal_le_ofReal
        unfold zWeight
        rw [if_pos (by linarith [hζ.1])]
        exact pow_le_pow_left₀ hTT.le (by linarith [hζ.1]) _
      · have hV : ζ ∉ {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} := hζ
        simp [Set.indicator_apply, hV]
    calc (0 : ℝ≥0∞) < ENNReal.ofReal ((T * T') ^ (k - 1)) *
          volume {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} :=
          ENNReal.mul_pos (ENNReal.ofReal_pos.2 (pow_pos hTT _)).ne' hVpos.ne'
      _ = ∫⁻ ζ, ENNReal.ofReal ((T * T') ^ (k - 1)) *
          {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.indicator 1 ζ := by
          rw [lintegral_const_mul _ (measurable_one.indicator hVo.measurableSet),
            lintegral_indicator_one hVo.measurableSet]
      _ ≤ _ := lintegral_mono hle
  · have hM : ∀ ζ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ ≤
        ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * (annU T T').indicator 1 ζ := by
      intro ζ
      by_cases hζ : ζ ∈ annU T T'
      · rw [Set.indicator_of_mem hζ, Pi.one_apply, mul_one, mul_one]
        apply ENNReal.ofReal_le_ofReal
        unfold zWeight
        rw [if_pos hζ.1.le]
        exact pow_le_pow_left₀ (by linarith [hζ.1]) (by linarith [hζ.2]) _
      · simp [Set.indicator_apply, hζ]
    have hsub : annU T T' ⊆ Metric.ball 0 (2 * Real.sqrt (T * T') + 1) := by
      intro ζ hζ
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : ‖ζ‖ ^ 2 < (2 * Real.sqrt (T * T')) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, mul_pow, Real.sq_sqrt hTT.le]
        linarith [hζ.2]
      have h2 := lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
      linarith
    have hfin : volume (annU T T') < ⊤ := (measure_mono hsub).trans_lt measure_ball_lt_top
    calc _ ≤ ∫⁻ ζ, ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * (annU T T').indicator 1 ζ :=
          lintegral_mono hM
      _ = ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * volume (annU T T') := by
          rw [lintegral_const_mul _ (measurable_one.indicator hAo.measurableSet),
            lintegral_indicator_one hAo.measurableSet]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/- English proof (translation)
Introduce `k r z z' μW μW' a a' μsec hW νg c hH hL hrep`. Establish `hg` using `gauge_of_lim νg hH hL`. Establish `hT` using `hW.T_pos`. Establish `hT'` using `hW.T'_pos`. Establish `hTT : 0 < Tz k r z * Tz k r z'` using `mul_pos hT hT'`.

Establish `hgm : Measurable ((annU (Tz k r z) (Tz k r z')).indicator (1 : ℂ → ℝ≥0∞))` using `measurable_one.indicator (annU_open _ _).measurableSet`. Establish `hφm : Measurable (fun x => (annU (Tz k r z) (Tz k r z')).indicator (1 : ℂ → ℝ≥0∞) (pairF k r z z' x))` using `hgm.comp (continuous_pairF k r z z').measurable`. Establish `h1` using `hR k r z z' μW μW' a a' μsec hW _ hgm`. Establish `h2` using `hP k r νg hW.k_pos hg z z' hW.z_mem hW.z'_mem hT hT' _ hgm`. Establish `h3` using `hrep _ hφm`.

Take `⟨hJ0, hJt⟩` from `testJ k (Tz k r z) (Tz k r z') hTT`. Rewrite `h1` using `[h3, h2, ← mul_assoc]`. Establish `h4` using `(ENNReal.mul_left_inj hJ0.ne' hJt.ne).1 h1`. Establish `hv` using `volU_pos k`. Establish `hv1` using `volU_pos (k - 1)`.

Establish `hpc : 0 < pairConst k (Tz k r z) (Tz k r z')`. Unfold `pairConst`. Check the signs of the components of the expression. Establish `ha` using `hW.a_pos`. Establish `ha'` using `hW.a'_pos`.

Establish `h5` using `congrArg ENNReal.toReal h4`. Rewrite `h5` using `[ENNReal.toReal_mul, ENNReal.toReal_ofReal hpc.le, ENNReal.toReal_ofReal (by positivity)]`. Establish `hc : c.toReal = a * a' / pairConst k (Tz k r z) (Tz k r z')`. Rewrite using `[← h5]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hc]`. Unfold `pairConst wbConst`. Establish `hTk : 0 < (Tz k r z * Tz k r z') ^ k` using `pow_pos hTT k`. Clear the denominators using the available nonvanishing facts.
-/
theorem constVal_of (hR : RhsTest) (hP : PairPush) : ConstVal := by
  intro k r z z' μW μW' a a' μsec hW νg c hH hL hrep
  have hg := gauge_of_lim νg hH hL
  have hT := hW.T_pos
  have hT' := hW.T'_pos
  have hTT : 0 < Tz k r z * Tz k r z' := mul_pos hT hT'
  have hgm : Measurable ((annU (Tz k r z) (Tz k r z')).indicator (1 : ℂ → ℝ≥0∞)) :=
    measurable_one.indicator (annU_open _ _).measurableSet
  have hφm : Measurable (fun x => (annU (Tz k r z) (Tz k r z')).indicator (1 : ℂ → ℝ≥0∞)
      (pairF k r z z' x)) := hgm.comp (continuous_pairF k r z z').measurable
  have h1 := hR k r z z' μW μW' a a' μsec hW _ hgm
  have h2 := hP k r νg hW.k_pos hg z z' hW.z_mem hW.z'_mem hT hT' _ hgm
  have h3 := hrep _ hφm
  obtain ⟨hJ0, hJt⟩ := testJ k (Tz k r z) (Tz k r z') hTT
  rw [h3, h2, ← mul_assoc] at h1

  have h4 := (ENNReal.mul_left_inj hJ0.ne' hJt.ne).1 h1
  have hv := volU_pos k
  have hv1 := volU_pos (k - 1)
  have hpc : 0 < pairConst k (Tz k r z) (Tz k r z') := by
    unfold pairConst
    positivity
  have ha := hW.a_pos
  have ha' := hW.a'_pos
  have h5 := congrArg ENNReal.toReal h4
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpc.le, ENNReal.toReal_ofReal (by positivity)] at h5
  have hc : c.toReal = a * a' / pairConst k (Tz k r z) (Tz k r z') := by
    rw [← h5]
    field_simp
  rw [hc]
  unfold pairConst wbConst
  have hTk : 0 < (Tz k r z * Tz k r z') ^ k := pow_pos hTT k
  field_simp

end PI.RhsWLim.W
