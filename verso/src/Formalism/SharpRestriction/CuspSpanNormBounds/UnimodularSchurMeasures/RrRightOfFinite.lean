import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs3

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}

/- English proof (translation)
Use `⟨fun g => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : μ D = 0`. Establish `hu : μ univ = 0`. Establish `hs : (univ : Set G) ⊆ ⋃ γ : Γ, (fun y => (γ : G) * y) ⁻¹' D` using `fun y _ => by`. Take `⟨γ, hγ, hD⟩` from `h.cov y`.

Conclude with `mem_iUnion.2 ⟨⟨γ, hγ⟩, hD⟩`. Use `measure_mono_null hs ?_` and prove the remaining obligations. Rewrite using `[measure_iUnion_null_iff]`. Introduce `γ`. Rewrite using `[measure_preimage_mul]`.

Conclude with `h0`. Establish `hz : μ = 0` using `Measure.measure_univ_eq_zero.1 hu`. Rewrite using `[hz]`. Simplify using the standard rewrite rules. Use `set ν := Measure.map (fun x => x * g) μ with hν`.

Establish `i1 : ν.IsMulLeftInvariant` using `isMulLeftInvariant_map_mul_right g`. Establish `i2 : SigmaFinite ν` using `(MeasurableEquiv.mulRight g).sigmaFinite_map (μ := μ)`. Establish `e` using `measure_eq_div_smul ν μ h0 hfin`. Establish `hD' : rr_FD μ Γ ((fun x => x * g) ⁻¹' D)` using `{ meas := (measurable_mul_const g) h.meas cov := fun y => by`. Take `⟨γ, hγ, hD⟩` from `h.cov (y * g)`.

Conclude with `⟨γ, hγ, by simpa [mul_assoc] using hD⟩`. Use `disj := fun γ hγ h1 => by`. Establish `hs : (fun y => γ * y) '' ((fun x => x * g) ⁻¹' D) ∩ (fun x => x * g) ⁻¹' D ⊆ (fun x => x * g) ⁻¹' ((fun y => γ * y) '' D ∩ D)`. Introduce and unpack `_ ⟨⟨y, hy, rfl⟩, h2⟩`. Conclude with `⟨⟨y * g, hy, by simp [mul_assoc]⟩, h2⟩`.

Use `measure_mono_null hs ?_` and prove the remaining obligations. Use `Measure.preimage_null_of_map_null (measurable_mul_const g).aemeasurable ?_` and prove the remaining obligations. Establish `e' : ν ((fun y => γ * y) '' D ∩ D) = ((ν D / μ D) • μ) ((fun y => γ * y) '' D ∩ D)` using `by rw [← e]`. Rewrite using `[← hν, e', Measure.smul_apply, h.disj γ hγ h1]`. Simplify using `}`.

Establish `hm : μ ((fun x => x * g) ⁻¹' D) = μ D` using `(rr_isFD hD').measure_eq (rr_isFD h)`. Establish `hνD : ν D = μ D` using `by rw [hν, Measure.map_apply (measurable_mul_const g) h.meas, hm]`. Rewrite using `[e, hνD, ENNReal.div_self h0 hfin, one_smul]`.
-/
theorem rr_right_of_finite [SigmaFinite μ] [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) (hfin : μ D ≠ ⊤) :
    μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  by_cases h0 : μ D = 0
  · have hu : μ univ = 0 := by
      have hs : (univ : Set G) ⊆ ⋃ γ : Γ, (fun y => (γ : G) * y) ⁻¹' D := fun y _ => by
        obtain ⟨γ, hγ, hD⟩ := h.cov y
        exact mem_iUnion.2 ⟨⟨γ, hγ⟩, hD⟩
      refine measure_mono_null hs ?_
      rw [measure_iUnion_null_iff]; intro γ
      rw [measure_preimage_mul]; exact h0
    have hz : μ = 0 := Measure.measure_univ_eq_zero.1 hu
    rw [hz]; simp
  · set ν := Measure.map (fun x => x * g) μ with hν
    have i1 : ν.IsMulLeftInvariant := isMulLeftInvariant_map_mul_right g
    have i2 : SigmaFinite ν := (MeasurableEquiv.mulRight g).sigmaFinite_map (μ := μ)
    have e := measure_eq_div_smul ν μ h0 hfin
    have hD' : rr_FD μ Γ ((fun x => x * g) ⁻¹' D) :=
      { meas := (measurable_mul_const g) h.meas
        cov := fun y => by
          obtain ⟨γ, hγ, hD⟩ := h.cov (y * g)
          exact ⟨γ, hγ, by simpa [mul_assoc] using hD⟩
        disj := fun γ hγ h1 => by
          have hs : (fun y => γ * y) '' ((fun x => x * g) ⁻¹' D) ∩ (fun x => x * g) ⁻¹' D ⊆
              (fun x => x * g) ⁻¹' ((fun y => γ * y) '' D ∩ D) := by
            rintro _ ⟨⟨y, hy, rfl⟩, h2⟩
            exact ⟨⟨y * g, hy, by simp [mul_assoc]⟩, h2⟩
          refine measure_mono_null hs ?_
          refine Measure.preimage_null_of_map_null (measurable_mul_const g).aemeasurable ?_
          have e' : ν ((fun y => γ * y) '' D ∩ D) = ((ν D / μ D) • μ) ((fun y => γ * y) '' D ∩ D) := by rw [← e]
          rw [← hν, e', Measure.smul_apply, h.disj γ hγ h1]
          simp }
    have hm : μ ((fun x => x * g) ⁻¹' D) = μ D := (rr_isFD hD').measure_eq (rr_isFD h)
    have hνD : ν D = μ D := by rw [hν, Measure.map_apply (measurable_mul_const g) h.meas, hm]
    rw [e, hνD, ENNReal.div_self h0 hfin, one_smul]

end Abs3

end Formalism.MainNotions.LeviCoordinates

end
