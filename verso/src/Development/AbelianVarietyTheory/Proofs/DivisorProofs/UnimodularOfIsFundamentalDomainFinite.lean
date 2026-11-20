import Mathlib
open scoped NNReal ENNReal
open MeasureTheory

/- English proof (translation)
Introduce `S _ _ _ _ _ _ _ _ Γ _ μS 𝓢 hH hF hfin`. Use `haveI : SMulInvariantMeasure Γ S μS := ⟨fun c s _ => by show μS ((fun x => (c : S) * x) ⁻¹' s) = μS s`. Conclude with `measure_preimage_mul μS (c : S) s⟩`. Establish `hpos : μS 𝓢 ≠ 0` using `hF.measure_ne_zero (NeZero.ne μS)`. Use `⟨fun g => ?_⟩` and prove the remaining obligations.

Establish `hmap` using `Measure.map_right_mul_eq_modularCharacterFun_smul μS g`. Establish `hF' : IsFundamentalDomain Γ ((fun x => x * g) ⁻¹' 𝓢) μS`. Use `hF.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_` and prove the remaining obligations. Conclude with `quasiMeasurePreserving_mul_right μS g`. Introduce `γ x show (γ : S) * x * g = (γ : S) * (x * g)`.

Conclude with `mul_assoc _ _ _`. Establish `heq : μS ((fun x => x * g) ⁻¹' 𝓢) = μS 𝓢` using `hF'.measure_eq hF`. Establish `h2 : (Measure.map (fun x => x * g) μS) 𝓢 = μS 𝓢`. Rewrite using `[show (fun x : S => x * g) = ⇑(MeasurableEquiv.mulRight g) from rfl, MeasurableEquiv.map_apply]`. Conclude with `heq`.

Rewrite `h2` using `[hmap]`. Rewrite `h2` using `[Measure.smul_apply]`. Establish `hc : (Measure.modularCharacterFun g : ℝ≥0∞) = 1`. Establish `h3 : (Measure.modularCharacterFun g : ℝ≥0∞) * μS 𝓢 = 1 * μS 𝓢`. Rewrite using `[one_mul]`.

Simplify `h2` using `[ENNReal.smul_def]`. Conclude with `(ENNReal.mul_left_inj hpos hfin).mp h3`. Rewrite `hmap` using `[show (fun x : S => x * g) = fun x => x * g from rfl]`. Rewrite using `[hmap]`. Establish `: Measure.modularCharacterFun g = 1` using `by exact_mod_cast hc`.

Rewrite using `[this, one_smul]`.
-/
theorem GlobalTheory.unimodular_of_isFundamentalDomain_finite : ∀ (S : Type) [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S] [T2Space S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S] (Γ : Subgroup S) [Countable Γ] (μS : Measure S) (𝓢 : Set S), μS.IsHaarMeasure → IsFundamentalDomain Γ 𝓢 μS → μS 𝓢 ≠ ⊤ → μS.IsMulRightInvariant := by
  intro S _ _ _ _ _ _ _ _ Γ _ μS 𝓢 hH hF hfin
  haveI : SMulInvariantMeasure Γ S μS :=
    ⟨fun c s _ => by
      show μS ((fun x => (c : S) * x) ⁻¹' s) = μS s
      exact measure_preimage_mul μS (c : S) s⟩
  have hpos : μS 𝓢 ≠ 0 := hF.measure_ne_zero (NeZero.ne μS)
  refine ⟨fun g => ?_⟩
  have hmap := Measure.map_right_mul_eq_modularCharacterFun_smul μS g

  have hF' : IsFundamentalDomain Γ ((fun x => x * g) ⁻¹' 𝓢) μS := by
    refine hF.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_
    · exact quasiMeasurePreserving_mul_right μS g
    · intro γ x
      show (γ : S) * x * g = (γ : S) * (x * g)
      exact mul_assoc _ _ _
  have heq : μS ((fun x => x * g) ⁻¹' 𝓢) = μS 𝓢 := hF'.measure_eq hF
  have h2 : (Measure.map (fun x => x * g) μS) 𝓢 = μS 𝓢 := by
    rw [show (fun x : S => x * g) = ⇑(MeasurableEquiv.mulRight g) from rfl, MeasurableEquiv.map_apply]
    exact heq
  rw [hmap] at h2
  rw [Measure.smul_apply] at h2
  have hc : (Measure.modularCharacterFun g : ℝ≥0∞) = 1 := by
    have h3 : (Measure.modularCharacterFun g : ℝ≥0∞) * μS 𝓢 = 1 * μS 𝓢 := by
      rw [one_mul]; simpa [ENNReal.smul_def] using h2
    exact (ENNReal.mul_left_inj hpos hfin).mp h3
  rw [show (fun x : S => x * g) = fun x => x * g from rfl] at hmap
  rw [hmap]
  have : Measure.modularCharacterFun g = 1 := by exact_mod_cast hc
  rw [this, one_smul]
