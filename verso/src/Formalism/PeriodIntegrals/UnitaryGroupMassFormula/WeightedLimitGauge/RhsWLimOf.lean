import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

/- English proof (translation)
Introduce `k r z z' μW μW' a a' μsec hD`. Establish `hk` using `hD.k_pos`. Take `⟨νg, hνg, ⟨ε, hε, hpos⟩, hlim⟩` from `hG k r hk`. Take `⟨ν, hν, ⟨ε', hε', hfin⟩, hrep⟩` from `hR k r z z' μW μW' a a' μsec hD`. Take `⟨c, hc, hνc⟩` from `hU k r ν νg hk hν hνg ⟨min ε ε', lt_min hε hε', fun ρ h0 hlt => ⟨hfin ρ h0 (lt_of_lt_of_le hlt (min_le_right _ _)), (hpos ρ h0 (lt_of_lt_of_le hlt (min_le_left _ _))).1, (hpos ρ h0 (lt_of_lt_of_le hlt (min_le_left _ _))).2⟩⟩`.

Establish `hrep' : ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → rhsW k r z z' μW μW' μsec φ = c * ∫⁻ x, φ x ∂νg`. Introduce `φ hφ`. Rewrite using `[hrep φ hφ, hνc, lintegral_smul_measure, smul_eq_mul]`. Establish `hcv` using `hC k r z z' μW μW' a a' μsec hD νg c hνg hlim hrep'`. Establish `hm` using `hM k r z z' μW μW' a a' μsec hD`.

Establish `hmeas : ∀ ρ, MeasurableSet (mBall k r z z' μsec ρ)` using `fun ρ => hB k r (mBase k r z z' μsec) ρ`. Establish `heq : ∀ ρ, (rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ = c.toReal * ((νg (tBall k r (mBase k r z z' μsec) ρ)).toReal / bVol k r ρ)`. Introduce `ρ`. Rewrite using `[hrep' _ (measurable_one.indicator (hmeas ρ)), lintegral_indicator_one (hmeas ρ), ENNReal.toReal_mul, mul_div_assoc]`. Apply the tactic sequence `all_goals rfl`.

Use `(tendsto_congr heq).2 ?_` and prove the remaining obligations. Rewrite using `[← hcv]`. Use `(hlim _ hm).const_mul c.toReal` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `this`.
-/
theorem rhsWLim_of (hM : MBaseMem) (hB : TBallMeas) (hG : GaugeExists) (hR : RhsHaar) (hU : HaarUniq)
    (hC : ConstVal) : RhsWLim := by
  intro k r z z' μW μW' a a' μsec hD
  have hk := hD.k_pos
  obtain ⟨νg, hνg, ⟨ε, hε, hpos⟩, hlim⟩ := hG k r hk
  obtain ⟨ν, hν, ⟨ε', hε', hfin⟩, hrep⟩ := hR k r z z' μW μW' a a' μsec hD
  obtain ⟨c, hc, hνc⟩ := hU k r ν νg hk hν hνg ⟨min ε ε', lt_min hε hε', fun ρ h0 hlt =>
    ⟨hfin ρ h0 (lt_of_lt_of_le hlt (min_le_right _ _)),
     (hpos ρ h0 (lt_of_lt_of_le hlt (min_le_left _ _))).1,
     (hpos ρ h0 (lt_of_lt_of_le hlt (min_le_left _ _))).2⟩⟩
  have hrep' : ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
      rhsW k r z z' μW μW' μsec φ = c * ∫⁻ x, φ x ∂νg := by
    intro φ hφ
    rw [hrep φ hφ, hνc, lintegral_smul_measure, smul_eq_mul]
  have hcv := hC k r z z' μW μW' a a' μsec hD νg c hνg hlim hrep'
  have hm := hM k r z z' μW μW' a a' μsec hD
  have hmeas : ∀ ρ, MeasurableSet (mBall k r z z' μsec ρ) := fun ρ => hB k r (mBase k r z z' μsec) ρ
  have heq : ∀ ρ, (rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ
      = c.toReal * ((νg (tBall k r (mBase k r z z' μsec) ρ)).toReal / bVol k r ρ) := by
    intro ρ
    rw [hrep' _ (measurable_one.indicator (hmeas ρ)), lintegral_indicator_one (hmeas ρ),
      ENNReal.toReal_mul, mul_div_assoc]
    all_goals rfl
  refine (tendsto_congr heq).2 ?_
  rw [← hcv]
  have := (hlim _ hm).const_mul c.toReal
  rw [mul_one] at this
  exact this

end PI.RhsWLim.W
