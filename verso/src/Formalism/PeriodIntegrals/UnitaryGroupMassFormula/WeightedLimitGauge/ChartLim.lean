import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace PI.RhsWLim.W

/- English proof (translation)
Introduce `E _ _ _ _ _ _ X _ Φ ν δ hδ hδ0 hν`. Take `⟨ε0, hε0, hν⟩` from `hν`. Rewrite using `[Metric.tendsto_nhdsWithin_nhds]`. Introduce `ε hε`. Establish `he : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2)` using `ENNReal.ofReal_pos.mpr (by linarith)`.

Establish `hnhds : Set.Icc (δ 0 - ENNReal.ofReal (ε / 2)) (δ 0 + ENNReal.ofReal (ε / 2)) ∈ 𝓝 (δ 0)` using `ENNReal.Icc_mem_nhds hδ0 he.ne'`. Take `⟨η1, hη1, hball⟩` from `Metric.mem_nhds_iff.mp (hδ hnhds)`. Use `⟨min η1 ε0, lt_min hη1 hε0, fun {ρ} hρ hdist => ?_⟩` and prove the remaining obligations. Establish `hρ0 : 0 < ρ` using `Set.mem_Ioi.mp hρ`. Establish `hρ' : ρ < min η1 ε0`.

Rewrite `hdist` using `[Real.dist_eq, sub_zero, abs_of_pos hρ0]`. Then use the resulting hypothesis. Establish `hρη : ρ < η1` using `lt_of_lt_of_le hρ' (min_le_left _ _)`. Establish `hρε : ρ < ε0` using `lt_of_lt_of_le hρ' (min_le_right _ _)`. Establish `hV0 : volume (Metric.ball (0 : E) ρ) ≠ 0` using `(Metric.measure_ball_pos volume (0 : E) hρ0).ne'`. Establish `hVt : volume (Metric.ball (0 : E) ρ) ≠ ⊤` using `measure_ball_lt_top.ne`.

Establish `hbd : ∀ x ∈ Metric.ball (0 : E) ρ, δ x ∈ Set.Icc (δ 0 - ENNReal.ofReal (ε / 2)) (δ 0 + ENNReal.ofReal (ε / 2))` using `fun x hx => hball (Metric.ball_subset_ball hρη.le hx)`. Establish `hup : ∫⁻ x in Metric.ball (0 : E) ρ, δ x ≤ (δ 0 + ENNReal.ofReal (ε / 2)) * volume (Metric.ball (0 : E) ρ)`. Combine the equalities or inequalities in the displayed calculation. Establish `hlo : (δ 0 - ENNReal.ofReal (ε / 2)) * volume (Metric.ball (0 : E) ρ) ≤ ∫⁻ x in Metric.ball (0 : E) ρ, δ x`. Combine the equalities or inequalities in the displayed calculation.

Establish `htop1 : δ 0 + ENNReal.ofReal (ε / 2) ≠ ⊤` using `ENNReal.add_ne_top.mpr ⟨hδ0, ENNReal.ofReal_ne_top⟩`. Establish `hAt : ∫⁻ x in Metric.ball (0 : E) ρ, δ x ≠ ⊤` using `ne_top_of_le_ne_top (ENNReal.mul_ne_top htop1 hVt) hup`. Establish `hVr : 0 < (volume (Metric.ball (0 : E) ρ)).toReal` using `ENNReal.toReal_pos hV0 hVt`. Establish `hupR : (∫⁻ x in Metric.ball (0 : E) ρ, δ x).toReal ≤ ((δ 0).toReal + ε / 2) * (volume (Metric.ball (0 : E) ρ)).toReal`. Establish `h1` using `ENNReal.toReal_mono (ENNReal.mul_ne_top htop1 hVt) hup`.

Rewrite `h1` using `[ENNReal.toReal_mul, ENNReal.toReal_add hδ0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by linarith)]`. Then use the resulting hypothesis. Establish `hloR : ((δ 0).toReal - ε / 2) * (volume (Metric.ball (0 : E) ρ)).toReal ≤ (∫⁻ x in Metric.ball (0 : E) ρ, δ x).toReal`. Establish `h1` using `ENNReal.toReal_mono hAt hlo`. Rewrite `h1` using `[ENNReal.toReal_mul]`. Establish `h2 : (δ 0).toReal - ε / 2 ≤ (δ 0 - ENNReal.ofReal (ε / 2)).toReal`.

Establish `h3` using `ENNReal.le_toReal_sub (a := δ 0) (b := ENNReal.ofReal (ε / 2)) ENNReal.ofReal_ne_top`. Rewrite `h3` using `[ENNReal.toReal_ofReal (by linarith)]`. Then use the resulting hypothesis. Conclude with `le_trans (mul_le_mul_of_nonneg_right h2 hVr.le) h1`. Establish `h4` using `(div_le_iff₀ hVr).mpr hupR`. Establish `h5` using `(le_div_iff₀ hVr).mpr hloR`.

Rewrite using `[hν ρ hρ0 hρε, Real.dist_eq, abs_lt]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem chartLim : ChartLim := by
  intro E _ _ _ _ _ _ X _ Φ ν δ hδ hδ0 hν
  obtain ⟨ε0, hε0, hν⟩ := hν
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have he : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  have hnhds : Set.Icc (δ 0 - ENNReal.ofReal (ε / 2)) (δ 0 + ENNReal.ofReal (ε / 2)) ∈ 𝓝 (δ 0) :=
    ENNReal.Icc_mem_nhds hδ0 he.ne'
  obtain ⟨η1, hη1, hball⟩ := Metric.mem_nhds_iff.mp (hδ hnhds)
  refine ⟨min η1 ε0, lt_min hη1 hε0, fun {ρ} hρ hdist => ?_⟩
  have hρ0 : 0 < ρ := Set.mem_Ioi.mp hρ
  have hρ' : ρ < min η1 ε0 := by
    rwa [Real.dist_eq, sub_zero, abs_of_pos hρ0] at hdist
  have hρη : ρ < η1 := lt_of_lt_of_le hρ' (min_le_left _ _)
  have hρε : ρ < ε0 := lt_of_lt_of_le hρ' (min_le_right _ _)
  have hV0 : volume (Metric.ball (0 : E) ρ) ≠ 0 := (Metric.measure_ball_pos volume (0 : E) hρ0).ne'
  have hVt : volume (Metric.ball (0 : E) ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hbd : ∀ x ∈ Metric.ball (0 : E) ρ,
      δ x ∈ Set.Icc (δ 0 - ENNReal.ofReal (ε / 2)) (δ 0 + ENNReal.ofReal (ε / 2)) :=
    fun x hx => hball (Metric.ball_subset_ball hρη.le hx)
  have hup : ∫⁻ x in Metric.ball (0 : E) ρ, δ x ≤
      (δ 0 + ENNReal.ofReal (ε / 2)) * volume (Metric.ball (0 : E) ρ) := by
    calc ∫⁻ x in Metric.ball (0 : E) ρ, δ x
        ≤ ∫⁻ _ in Metric.ball (0 : E) ρ, (δ 0 + ENNReal.ofReal (ε / 2)) :=
          setLIntegral_mono' measurableSet_ball fun x hx => (hbd x hx).2
      _ = (δ 0 + ENNReal.ofReal (ε / 2)) * volume (Metric.ball (0 : E) ρ) := setLIntegral_const _ _
  have hlo : (δ 0 - ENNReal.ofReal (ε / 2)) * volume (Metric.ball (0 : E) ρ) ≤
      ∫⁻ x in Metric.ball (0 : E) ρ, δ x := by
    calc (δ 0 - ENNReal.ofReal (ε / 2)) * volume (Metric.ball (0 : E) ρ)
        = ∫⁻ _ in Metric.ball (0 : E) ρ, (δ 0 - ENNReal.ofReal (ε / 2)) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in Metric.ball (0 : E) ρ, δ x :=
          setLIntegral_mono' measurableSet_ball fun x hx => (hbd x hx).1
  have htop1 : δ 0 + ENNReal.ofReal (ε / 2) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hδ0, ENNReal.ofReal_ne_top⟩
  have hAt : ∫⁻ x in Metric.ball (0 : E) ρ, δ x ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top htop1 hVt) hup
  have hVr : 0 < (volume (Metric.ball (0 : E) ρ)).toReal := ENNReal.toReal_pos hV0 hVt
  have hupR : (∫⁻ x in Metric.ball (0 : E) ρ, δ x).toReal ≤
      ((δ 0).toReal + ε / 2) * (volume (Metric.ball (0 : E) ρ)).toReal := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top htop1 hVt) hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_add hδ0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)] at h1
  have hloR : ((δ 0).toReal - ε / 2) * (volume (Metric.ball (0 : E) ρ)).toReal ≤
      (∫⁻ x in Metric.ball (0 : E) ρ, δ x).toReal := by
    have h1 := ENNReal.toReal_mono hAt hlo
    rw [ENNReal.toReal_mul] at h1
    have h2 : (δ 0).toReal - ε / 2 ≤ (δ 0 - ENNReal.ofReal (ε / 2)).toReal := by
      have h3 := ENNReal.le_toReal_sub (a := δ 0) (b := ENNReal.ofReal (ε / 2)) ENNReal.ofReal_ne_top
      rwa [ENNReal.toReal_ofReal (by linarith)] at h3
    exact le_trans (mul_le_mul_of_nonneg_right h2 hVr.le) h1
  have h4 := (div_le_iff₀ hVr).mpr hupR
  have h5 := (le_div_iff₀ hVr).mpr hloR
  rw [hν ρ hρ0 hρε, Real.dist_eq, abs_lt]
  constructor <;> linarith

end PI.RhsWLim.W
