import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOneStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOneStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSummableMajorantRationalVectorsLocallyUnifStatement
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ N hF Φ hΦ`. Take `⟨hc, ⟨K, hK, hKz⟩, hdec⟩` from `hΦ`. Take `⟨k, hk⟩` from `GlobalTheory.T.exists_summableMajorant_rationalVectors_locallyUniform F N hF K hK`. Take `⟨C, hC⟩` from `hdec k`. Establish `hsz : ∀ u : Fin N → AF F, 0 ≤ sz u` using `fun u => Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun w _ => abs_nonneg _`.

Establish `hC0 : 0 ≤ C` using `le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [hsz 0]) k)) (hC 0)`. Establish `key : ∀ ω : Set (Fin N → AF F), IsCompact ω → ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧ ∀ ξ, ∀ y ∈ ω, ‖Φ (rat ξ + y)‖ ≤ C * c ξ`. Introduce `ω hω`. Take `⟨c, hcs, hc0, hcb⟩` from `hk ω hω`. Use `⟨c, hcs, hc0, fun ξ y hy => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hmem : fin (rat ξ + y) ∈ K`. Establish `h1` using `hcb ξ y hy hmem`. Establish `h2` using `hC (rat ξ + y)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hKz _ hmem, norm_zero]`.

Conclude with `mul_nonneg hC0 (hc0 ξ)`. Use `haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `μ hμ`. Take `⟨ν, hν⟩` from `GlobalTheory.T.exists_measure_isCov1 F`.

Take `⟨-, -, -, ⟨K₀, hK₀, hcov⟩, -⟩` from `GlobalTheory.T.rationalVectors_adeles_fundamentalDomain_mass_one F N ν hν`. Take `⟨c, hcs, hc0, hcb⟩` from `key K₀ hK₀`. Use `⟨hc.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Set `S : (Fin N → F) → Set (Fin N → AF F)` to `fun ξ => (fun u => u + -rat ξ) ⁻¹' K₀`. Establish `hSm : ∀ ξ, MeasurableSet (S ξ)` using `fun ξ => hK₀.measurableSet.preimage (measurable_add_const _)`.

Establish `hSμ : ∀ ξ, μ (S ξ) = μ K₀` using `fun ξ => measure_preimage_add_right μ (-rat ξ) K₀`. Establish `hpt : ∀ u, ‖Φ u‖ₑ ≤ ∑' ξ, (S ξ).indicator (fun _ => ENNReal.ofReal (C * c ξ)) u`. Introduce `u`. Take `⟨ξ, hξ⟩` from `hcov u`. Establish `hu : u ∈ S ξ` using `by show u + -rat ξ ∈ K₀`.

Rewrite using `[← sub_eq_add_neg]`. Conclude with `hξ`. Use `le_trans ?_ (ENNReal.le_tsum ξ)` and prove the remaining obligations. Rewrite using `[Set.indicator_of_mem hu]`. Establish `h3` using `hcb ξ (u - rat ξ) hξ`.

Rewrite `h3` using `[add_sub_cancel]`. Rewrite using `[← ofReal_norm_eq_enorm]`. Conclude with `ENNReal.ofReal_le_ofReal h3`. Establish `hfin : (∑' ξ, ENNReal.ofReal (C * c ξ)) < ∞`. Rewrite using `[← ENNReal.ofReal_tsum_of_nonneg (fun ξ => mul_nonneg hC0 (hc0 ξ)) (hcs.mul_left C)]`.

Conclude with `ENNReal.ofReal_lt_top`. Unfold `HasFiniteIntegral`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `ξ`.

Rewrite using `[lintegral_indicator_const (hSm ξ), hSμ]`. Use `_ = (∑' ξ, ENNReal.ofReal (C * c ξ)) * μ K₀ := ENNReal.tsum_mul_right`. Use `_ < ∞ := ENNReal.mul_lt_top hfin hK₀.measure_lt_top`. Introduce `u`. Take `⟨c, hcs, hc0, hcb⟩` from `key {u} isCompact_singleton`.

Conclude with `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hcb ξ u rfl) (hcs.mul_left C)`. Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Take `⟨ω, hωc, hωn⟩` from `exists_compact_mem_nhds x`. Take `⟨c, hcs, hc0, hcb⟩` from `key ω hωc`. Establish `hon : ContinuousOn (fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u)) ω` using `continuousOn_tsum (fun ξ => (hc.comp (continuous_const.add continuous_id)).continuousOn) (hcs.mul_left C) (fun ξ y hy => hcb ξ y hy)`.

Conclude with `hon.continuousAt hωn`.
-/
theorem decay_integrable_periodise : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ →
      (∀ μ : Measure (Fin N → AF F), μ.IsAddHaarMeasure → Integrable Φ μ) ∧
      (∀ u, Summable fun ξ : Fin N → F => ‖Φ (rat ξ + u)‖) ∧
      Continuous fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u) := by
  intro F _ _ N hF Φ hΦ
  obtain ⟨hc, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_summableMajorant_rationalVectors_locallyUniform F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hsz : ∀ u : Fin N → AF F, 0 ≤ sz u := fun u =>
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun w _ => abs_nonneg _
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [hsz 0]) k)) (hC 0)
  have key : ∀ ω : Set (Fin N → AF F), IsCompact ω → ∃ c : (Fin N → F) → ℝ, Summable c ∧
      (∀ ξ, 0 ≤ c ξ) ∧ ∀ ξ, ∀ y ∈ ω, ‖Φ (rat ξ + y)‖ ≤ C * c ξ := by
    intro ω hω
    obtain ⟨c, hcs, hc0, hcb⟩ := hk ω hω
    refine ⟨c, hcs, hc0, fun ξ y hy => ?_⟩
    by_cases hmem : fin (rat ξ + y) ∈ K
    · have h1 := hcb ξ y hy hmem
      have h2 := hC (rat ξ + y)
      calc ‖Φ (rat ξ + y)‖ = ‖Φ (rat ξ + y)‖ * 1 := (mul_one _).symm
        _ ≤ ‖Φ (rat ξ + y)‖ * (c ξ * (1 + sz (rat ξ + y)) ^ k) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = c ξ * (‖Φ (rat ξ + y)‖ * (1 + sz (rat ξ + y)) ^ k) := by ring
        _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
        _ = C * c ξ := mul_comm _ _
    · rw [hKz _ hmem, norm_zero]
      exact mul_nonneg hC0 (hc0 ξ)
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  refine ⟨?_, ?_, ?_⟩
  · intro μ hμ
    obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_measure_isCov1 F
    obtain ⟨-, -, -, ⟨K₀, hK₀, hcov⟩, -⟩ := GlobalTheory.T.rationalVectors_adeles_fundamentalDomain_mass_one F N ν hν
    obtain ⟨c, hcs, hc0, hcb⟩ := key K₀ hK₀
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    let S : (Fin N → F) → Set (Fin N → AF F) := fun ξ => (fun u => u + -rat ξ) ⁻¹' K₀
    have hSm : ∀ ξ, MeasurableSet (S ξ) := fun ξ =>
      hK₀.measurableSet.preimage (measurable_add_const _)
    have hSμ : ∀ ξ, μ (S ξ) = μ K₀ := fun ξ => measure_preimage_add_right μ (-rat ξ) K₀
    have hpt : ∀ u, ‖Φ u‖ₑ ≤ ∑' ξ, (S ξ).indicator (fun _ => ENNReal.ofReal (C * c ξ)) u := by
      intro u
      obtain ⟨ξ, hξ⟩ := hcov u
      have hu : u ∈ S ξ := by
        show u + -rat ξ ∈ K₀
        rw [← sub_eq_add_neg]; exact hξ
      refine le_trans ?_ (ENNReal.le_tsum ξ)
      rw [Set.indicator_of_mem hu]
      have h3 := hcb ξ (u - rat ξ) hξ
      rw [add_sub_cancel] at h3
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal h3
    have hfin : (∑' ξ, ENNReal.ofReal (C * c ξ)) < ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun ξ => mul_nonneg hC0 (hc0 ξ)) (hcs.mul_left C)]
      exact ENNReal.ofReal_lt_top
    unfold HasFiniteIntegral
    calc ∫⁻ u, ‖Φ u‖ₑ ∂μ
        ≤ ∫⁻ u, ∑' ξ, (S ξ).indicator (fun _ => ENNReal.ofReal (C * c ξ)) u ∂μ := lintegral_mono hpt
      _ = ∑' ξ, ∫⁻ u, (S ξ).indicator (fun _ => ENNReal.ofReal (C * c ξ)) u ∂μ :=
          lintegral_tsum fun ξ => (measurable_const.indicator (hSm ξ)).aemeasurable
      _ = ∑' ξ, ENNReal.ofReal (C * c ξ) * μ K₀ := by
          congr 1; ext ξ; rw [lintegral_indicator_const (hSm ξ), hSμ]
      _ = (∑' ξ, ENNReal.ofReal (C * c ξ)) * μ K₀ := ENNReal.tsum_mul_right
      _ < ∞ := ENNReal.mul_lt_top hfin hK₀.measure_lt_top
  · intro u
    obtain ⟨c, hcs, hc0, hcb⟩ := key {u} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hcb ξ u rfl) (hcs.mul_left C)
  · refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨ω, hωc, hωn⟩ := exists_compact_mem_nhds x
    obtain ⟨c, hcs, hc0, hcb⟩ := key ω hωc
    have hon : ContinuousOn (fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u)) ω :=
      continuousOn_tsum (fun ξ => (hc.comp (continuous_const.add continuous_id)).continuousOn)
        (hcs.mul_left C) (fun ξ y hy => hcb ξ y hy)
    exact hon.continuousAt hωn

end GlobalTheory
