import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntSphere
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set MvPolynomial

noncomputable section

namespace LogInt

variable {n k : ℕ}

def ballSet (h : HermNorm n) (k : ℕ) : Set (Fin k × Fin n → ℂ) :=
  {u | ∀ i, h.norm (fun j => u (i, j)) < 1}

/- English proof (translation)
Establish `e : ballSet h k = ⋂ i, {u : Fin k × Fin n → ℂ | h.norm (fun j => u (i, j)) < 1}`. Use extensionality with `u`. Simplify using `[ballSet]`. Rewrite using `[e]`. Conclude with `MeasurableSet.iInter fun i => measurableSet_lt (measurable_groupNorm h i) measurable_const`.
-/
theorem measurableSet_ballSet (h : HermNorm n) : MeasurableSet (ballSet h k) := by
  have e : ballSet h k = ⋂ i, {u : Fin k × Fin n → ℂ | h.norm (fun j => u (i, j)) < 1} := by
    ext u; simp [ballSet]
  rw [e]
  exact MeasurableSet.iInter fun i => measurableSet_lt (measurable_groupNorm h i) measurable_const

/- English proof (translation)
Introduce `u hu`. Simplify using `only [polydisc, mem_univ_pi, Metric.mem_closedBall, dist_zero_right]`. Introduce `ij`. Conclude with `(hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)`.
-/
theorem ballSet_subset_polydisc (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballSet h k ⊆ polydisc _ C := by
  intro u hu
  simp only [polydisc, mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  intro ij
  exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)

/- English proof (translation)
Use function extensionality and compare the values at `ij`. Simplify using `[normT]`.
-/
theorem normT_univ (h : HermNorm n) (u : Fin k × Fin n → ℂ) :
    normT h Finset.univ u = fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij := by
  funext ij
  simp [normT]

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `h.li_exists_coord_le`. Take `⟨h1, h2⟩` from `logNormT h C hC0 hC Finset.univ f hf`. Simplify using `only [normT_univ] at h1 h2`. Conclude with `⟨h1.mono_set (ballSet_subset_polydisc h C hC0 hC), ae_restrict_of_ae_restrict_of_subset (ballSet_subset_polydisc h C hC0 hC) h2⟩`.
-/
theorem integrableOn_log_mahler (h : HermNorm n) (f : MvPolynomial (Fin k × Fin n) ℂ) (hf : f ≠ 0) :
    IntegrableOn (fun u : Fin k × Fin n → ℂ =>
        Real.log ‖eval (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij) f‖)
        (ballSet h k) ∧
      ∀ᵐ u ∂(volume.restrict (ballSet h k)),
        eval (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij) f ≠ 0 := by
  obtain ⟨C, hC0, hC⟩ := h.li_exists_coord_le
  obtain ⟨h1, h2⟩ := logNormT h C hC0 hC Finset.univ f hf
  simp only [normT_univ] at h1 h2
  exact ⟨h1.mono_set (ballSet_subset_polydisc h C hC0 hC),
    ae_restrict_of_ae_restrict_of_subset (ballSet_subset_polydisc h C hC0 hC) h2⟩

end LogInt

/- English proof (translation)
Introduce `n k h f g hf hg`. Take `⟨i1, z1⟩` from `LogInt.integrableOn_log_mahler h f hf`. Take `⟨i2, z2⟩` from `LogInt.integrableOn_log_mahler h g hg`. Unfold `mahler sphereMean`. Express the relevant statement in the definitionally equal form `⨍ u in LogInt.ballSet h k, _ = (⨍ u in LogInt.ballSet h k, _) + ⨍ u in LogInt.ballSet h k, _`.

Rewrite using `[setAverage_eq, setAverage_eq, setAverage_eq, ← smul_add, ← integral_add i1 i2]`. Use `congr 1`. Use `setIntegral_congr_ae (LogInt.measurableSet_ballSet h) ?_` and prove the remaining obligations. Use `(ae_restrict_iff' (LogInt.measurableSet_ballSet h)).mp (z1.and z2)` as an intermediate fact. Use `filter_upwards [this] with u hu hB`.

Take `⟨h1, h2⟩` from `hu hB`. Rewrite using `[map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)]`.
-/
theorem mahlerMul : MahlerMul.Statement := by
  intro n k h f g hf hg
  obtain ⟨i1, z1⟩ := LogInt.integrableOn_log_mahler h f hf
  obtain ⟨i2, z2⟩ := LogInt.integrableOn_log_mahler h g hg
  unfold mahler sphereMean
  change ⨍ u in LogInt.ballSet h k, _ = (⨍ u in LogInt.ballSet h k, _) + ⨍ u in LogInt.ballSet h k, _
  rw [setAverage_eq, setAverage_eq, setAverage_eq, ← smul_add, ← integral_add i1 i2]
  congr 1
  refine setIntegral_congr_ae (LogInt.measurableSet_ballSet h) ?_
  have := (ae_restrict_iff' (LogInt.measurableSet_ballSet h)).mp (z1.and z2)
  filter_upwards [this] with u hu hB
  obtain ⟨h1, h2⟩ := hu hB
  rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)]

end

end GroundTheory.Heights₂.Heights
