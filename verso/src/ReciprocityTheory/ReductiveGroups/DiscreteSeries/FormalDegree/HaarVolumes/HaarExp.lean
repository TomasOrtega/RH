import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExpD

noncomputable section

open Finset Matrix MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HExp

variable {n : ℕ}

section Normed

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Use `letI mV : MeasurableSpace (gV ε) := borel _`. Use `haveI : BorelSpace (gV ε) := ⟨rfl⟩`. Set `eC : GCo ε ≃L[ℝ] gV ε` to `(gE ε).toContinuousLinearEquiv`. Set `lam : Measure (gV ε)` to `Measure.map eC volume`. Use `haveI : (volume : Measure (KCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _`.

Use `haveI : (volume : Measure (GCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _`. Establish `hlamH : lam.IsAddHaarMeasure` using `eC.isAddHaarMeasure_map volume`. Take `⟨c, hc0, hct, hup, hdown⟩` from `(ujChart ε).exists_density_unif' inferInstance mV ⟨rfl⟩ _ inferInstance inferInstance μ inferInstance lam (by exact hlamH)`. Establish `himg : ∀ S : Set (GCo ε), (ujChart ε).img (eC '' S) = expSet S`. Introduce `S`.

Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨s, hs, rfl⟩, h⟩`. Conclude with `⟨s, hs, h⟩`. Introduce and unpack `⟨s, hs, h⟩`.

Conclude with `⟨eC s, ⟨s, hs, rfl⟩, h⟩`. Establish `hmeas : ∀ S : Set (GCo ε), MeasurableSet S → MeasurableSet (eC '' S)` using `fun S hS => eC.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hS`. Establish `hlam : ∀ S : Set (GCo ε), MeasurableSet S → lam (eC '' S) = volume S`. Introduce `S hS`. Rewrite using `[Measure.map_apply eC.continuous.measurable (hmeas S hS), Set.preimage_image_eq S eC.injective]`.

Establish `hsmall : ∀ δ > 0, ∃ δ' > 0, ∀ S : Set (GCo ε), (∀ s ∈ S, ‖s‖ < δ') → eC '' S ⊆ ball (0 : gV ε) δ`. Introduce `δ hδ`. Take `⟨δ', hδ', h⟩` from `Metric.continuousAt_iff.mp (eC.continuous.continuousAt (x := 0)) δ hδ`. Use `⟨δ', hδ', fun S hS => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨s, hs, rfl⟩`.

Use `h (x := s) (by simpa using hS s hs)` as an intermediate fact. Simplify using `using this`. Use `set d := c.toReal with hd`. Establish `hdpos : 0 < d` using `ENNReal.toReal_pos hc0 hct`. Establish `hc : c = ENNReal.ofReal d` using `(ENNReal.ofReal_toReal hct).symm`.

Use `⟨d, hdpos, fun η hη => ?_⟩` and prove the remaining obligations. Establish `hU : ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) → μ (expSet S) ≤ ENNReal.ofReal ((1 + η) * d) * volume S`. Take `⟨δ, hδ, h⟩` from `hup (Real.toNNReal ((1 + η) * d)) (by`. Rewrite using `[hc]`. Use `show ENNReal.ofReal d < ENNReal.ofReal ((1 + η) * d)`.

Rewrite using `[ENNReal.ofReal_lt_ofReal_iff (by positivity)]`. Use the proof step `nlinarith)`. Take `⟨δ', hδ', h'⟩` from `hsmall δ hδ`. Use `⟨δ', hδ', fun S hS hSδ => ?_⟩` and prove the remaining obligations. Use `h (eC '' S) (hmeas S hS) (h' S hSδ)` as an intermediate fact.

Rewrite `this` using `[himg, hlam S hS]`. Conclude with `this`. Establish `hL : ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) → ENNReal.ofReal ((1 - η) * d) * volume S ≤ μ (expSet S)`. Distinguish the cases in `hη1 : (1 - η) * d ≤ 0`. Use `⟨1, one_pos, fun S _ _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[ENNReal.ofReal_of_nonpos hη1, zero_mul]`. Conclude with `bot_le`. Establish `hη1' : 0 < (1 - η) * d` using `not_le.mp hη1`. Take `⟨δ, hδ, h⟩` from `hdown (Real.toNNReal ((1 - η) * d)) (by`. Rewrite using `[hc]`.

Use `show ENNReal.ofReal ((1 - η) * d) < ENNReal.ofReal d`. Rewrite using `[ENNReal.ofReal_lt_ofReal_iff hdpos]`. Use the proof step `nlinarith)`. Take `⟨δ', hδ', h'⟩` from `hsmall δ hδ`. Use `⟨δ', hδ', fun S hS hSδ => ?_⟩` and prove the remaining obligations.

Use `h (eC '' S) (hmeas S hS) (h' S hSδ)` as an intermediate fact. Rewrite `this` using `[himg, hlam S hS]`. Conclude with `this`. Take `⟨δ1, hδ1, h1⟩` from `hU`. Take `⟨δ2, hδ2, h2⟩` from `hL`.

Use `⟨min δ1 δ2, lt_min hδ1 hδ2, fun S hS hSδ => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `h1 S hS fun s hs => lt_of_lt_of_le (hSδ s hs) (min_le_left _ _)`. Conclude with `h2 S hS fun s hs => lt_of_lt_of_le (hSδ s hs) (min_le_right _ _)`.
-/
theorem haar_exp_density {ε : Fin n → Bool} (μ : Measure (UJ ε)) [μ.IsHaarMeasure] :
    ∃ d : ℝ, 0 < d ∧ DensOn (fun S => μ (expSet S)) d := by
  letI mV : MeasurableSpace (gV ε) := borel _
  haveI : BorelSpace (gV ε) := ⟨rfl⟩
  let eC : GCo ε ≃L[ℝ] gV ε := (gE ε).toContinuousLinearEquiv
  let lam : Measure (gV ε) := Measure.map eC volume
  haveI : (volume : Measure (KCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  haveI : (volume : Measure (GCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hlamH : lam.IsAddHaarMeasure := eC.isAddHaarMeasure_map volume
  obtain ⟨c, hc0, hct, hup, hdown⟩ := (ujChart ε).exists_density_unif' inferInstance mV ⟨rfl⟩ _
    inferInstance inferInstance μ inferInstance lam (by exact hlamH)
  have himg : ∀ S : Set (GCo ε), (ujChart ε).img (eC '' S) = expSet S := by
    intro S
    ext g
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, h⟩
      exact ⟨s, hs, h⟩
    · rintro ⟨s, hs, h⟩
      exact ⟨eC s, ⟨s, hs, rfl⟩, h⟩
  have hmeas : ∀ S : Set (GCo ε), MeasurableSet S → MeasurableSet (eC '' S) := fun S hS =>
    eC.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hS
  have hlam : ∀ S : Set (GCo ε), MeasurableSet S → lam (eC '' S) = volume S := by
    intro S hS
    rw [Measure.map_apply eC.continuous.measurable (hmeas S hS), Set.preimage_image_eq S eC.injective]
  have hsmall : ∀ δ > 0, ∃ δ' > 0, ∀ S : Set (GCo ε), (∀ s ∈ S, ‖s‖ < δ') →
      eC '' S ⊆ ball (0 : gV ε) δ := by
    intro δ hδ
    obtain ⟨δ', hδ', h⟩ := Metric.continuousAt_iff.mp (eC.continuous.continuousAt (x := 0)) δ hδ
    refine ⟨δ', hδ', fun S hS => ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have := h (x := s) (by simpa using hS s hs)
    simpa using this
  set d := c.toReal with hd
  have hdpos : 0 < d := ENNReal.toReal_pos hc0 hct
  have hc : c = ENNReal.ofReal d := (ENNReal.ofReal_toReal hct).symm
  refine ⟨d, hdpos, fun η hη => ?_⟩
  have hU : ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
      μ (expSet S) ≤ ENNReal.ofReal ((1 + η) * d) * volume S := by
    obtain ⟨δ, hδ, h⟩ := hup (Real.toNNReal ((1 + η) * d)) (by
      rw [hc]
      show ENNReal.ofReal d < ENNReal.ofReal ((1 + η) * d)
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      nlinarith)
    obtain ⟨δ', hδ', h'⟩ := hsmall δ hδ
    refine ⟨δ', hδ', fun S hS hSδ => ?_⟩
    have := h (eC '' S) (hmeas S hS) (h' S hSδ)
    rw [himg, hlam S hS] at this
    exact this
  have hL : ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
      ENNReal.ofReal ((1 - η) * d) * volume S ≤ μ (expSet S) := by
    by_cases hη1 : (1 - η) * d ≤ 0
    · refine ⟨1, one_pos, fun S _ _ => ?_⟩
      rw [ENNReal.ofReal_of_nonpos hη1, zero_mul]
      exact bot_le
    · have hη1' : 0 < (1 - η) * d := not_le.mp hη1
      obtain ⟨δ, hδ, h⟩ := hdown (Real.toNNReal ((1 - η) * d)) (by
        rw [hc]
        show ENNReal.ofReal ((1 - η) * d) < ENNReal.ofReal d
        rw [ENNReal.ofReal_lt_ofReal_iff hdpos]
        nlinarith)
      obtain ⟨δ', hδ', h'⟩ := hsmall δ hδ
      refine ⟨δ', hδ', fun S hS hSδ => ?_⟩
      have := h (eC '' S) (hmeas S hS) (h' S hSδ)
      rw [himg, hlam S hS] at this
      exact this
  obtain ⟨δ1, hδ1, h1⟩ := hU
  obtain ⟨δ2, hδ2, h2⟩ := hL
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun S hS hSδ => ⟨?_, ?_⟩⟩
  · exact h1 S hS fun s hs => lt_of_lt_of_le (hSδ s hs) (min_le_left _ _)
  · exact h2 S hS fun s hs => lt_of_lt_of_le (hSδ s hs) (min_le_right _ _)

end Normed

end ReciprocityTheory.ChartRestriction.DS
