import Mathlib

noncomputable section

namespace PI.IwaMeasEx.MG

open MeasureTheory Measure Topology Set
open scoped ENNReal NNReal

/- English proof (translation)
Take `⟨x⟩` from `‹Nonempty Y›`. Take `⟨K, hK, hKx⟩` from `exists_compact_mem_nhds x`. Establish `h0 : ρ K ≠ 0` using `(measure_pos_of_mem_nhds ρ hKx).ne'`. Establish `htop : ρ K ≠ ∞` using `hK.measure_lt_top.ne`. Establish `hK' : (a : ℝ≥0∞) * ρ K = (b : ℝ≥0∞) * ρ K`.

Establish `e` using `congrArg (fun m : Measure Y => m K) h`. Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e`. Conclude with `e`. Establish `hab : (a : ℝ≥0∞) = b` using `(ENNReal.mul_left_inj h0 htop).mp hK'`. Conclude with `hab` after adjusting the coercions.
-/
theorem smul_cancel {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [LocallyCompactSpace Y]
    (ρ : Measure Y) [IsFiniteMeasureOnCompacts ρ] [ρ.IsOpenPosMeasure] [Nonempty Y] {a b : ℝ≥0}
    (h : a • ρ = b • ρ) : a = b := by
  obtain ⟨x⟩ := ‹Nonempty Y›
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  have h0 : ρ K ≠ 0 := (measure_pos_of_mem_nhds ρ hKx).ne'
  have htop : ρ K ≠ ∞ := hK.measure_lt_top.ne
  have hK' : (a : ℝ≥0∞) * ρ K = (b : ℝ≥0∞) * ρ K := by
    have e := congrArg (fun m : Measure Y => m K) h
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
    exact e
  have hab : (a : ℝ≥0∞) = b := (ENNReal.mul_left_inj h0 htop).mp hK'
  exact_mod_cast hab

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
variable {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [IsTopologicalAddGroup Y] [LocallyCompactSpace Y]

/- English proof (translation)
Establish `hφ : Measurable φ` using `(map_continuous φ).measurable`. Establish `hL : Measurable L` using `(map_continuous L).measurable`. Establish `hcomp : χ ∘ φ = L ∘ χ` using `funext h`. Establish `h1 : mulEquivHaarChar φ • map L ν = ν`. Establish `e` using `congrArg (Measure.map χ) (mulEquivHaarChar_smul_map μ φ)`.

Rewrite `e` using `[Measure.map_smul, Measure.map_map hχm hφ, hcomp, ← Measure.map_map hL hχm, hχ]`. Conclude with `e`. Establish `h2 : addEquivAddHaarChar L • map L ν = ν` using `addEquivAddHaarChar_smul_map ν L`. Establish `h3 : addEquivAddHaarChar L • ν = mulEquivHaarChar φ • ν`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[smul_smul, smul_smul, mul_comm]`. Use `_ = mulEquivHaarChar φ • ν := by rw [h2]`. Conclude with `(smul_cancel ν h3).symm`.
-/
theorem mulEquivHaarChar_eq_of_chart (μ : Measure G) [IsHaarMeasure μ] [Regular μ] (ν : Measure Y)
    [IsAddHaarMeasure ν] [Regular ν] (χ : G → Y) (hχm : Measurable χ) (hχ : μ.map χ = ν) (φ : G ≃ₜ* G)
    (L : Y ≃ₜ+ Y) (h : ∀ x, χ (φ x) = L (χ x)) : mulEquivHaarChar φ = addEquivAddHaarChar L := by
  have hφ : Measurable φ := (map_continuous φ).measurable
  have hL : Measurable L := (map_continuous L).measurable
  have hcomp : χ ∘ φ = L ∘ χ := funext h
  have h1 : mulEquivHaarChar φ • map L ν = ν := by
    have e := congrArg (Measure.map χ) (mulEquivHaarChar_smul_map μ φ)
    rw [Measure.map_smul, Measure.map_map hχm hφ, hcomp, ← Measure.map_map hL hχm, hχ] at e
    exact e
  have h2 : addEquivAddHaarChar L • map L ν = ν := addEquivAddHaarChar_smul_map ν L
  have h3 : addEquivAddHaarChar L • ν = mulEquivHaarChar φ • ν := by
    calc addEquivAddHaarChar L • ν = addEquivAddHaarChar L • (mulEquivHaarChar φ • map L ν) := by rw [h1]
      _ = mulEquivHaarChar φ • (addEquivAddHaarChar L • map L ν) := by
        rw [smul_smul, smul_smul, mul_comm]
      _ = mulEquivHaarChar φ • ν := by rw [h2]
  exact (smul_cancel ν h3).symm

/- English proof (translation)
Establish `hm : Measurable (fun p : A × B => (p.1, p.2 + f p.1))` using `measurable_fst.prodMk (measurable_snd.add (hf.comp measurable_fst))`. Use extensionality with `s hs`. Rewrite using `[Measure.map_apply hm hs, Measure.prod_apply hs, Measure.prod_apply (hm hs)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Establish `hpre : Prod.mk x ⁻¹' ((fun p : A × B => (p.1, p.2 + f p.1)) ⁻¹' s) = (fun b => b + f x) ⁻¹' (Prod.mk x ⁻¹' s)` using `rfl`.

Rewrite using `[hpre, measure_preimage_add_right]`.
-/
theorem shear_map {A B : Type*} [MeasurableSpace A] [AddGroup B] [MeasurableSpace B] [MeasurableAdd₂ B]
    [MeasurableAdd B] (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] [ν.IsAddRightInvariant]
    (f : A → B) (hf : Measurable f) :
    (μ.prod ν).map (fun p : A × B => (p.1, p.2 + f p.1)) = μ.prod ν := by
  have hm : Measurable (fun p : A × B => (p.1, p.2 + f p.1)) :=
    measurable_fst.prodMk (measurable_snd.add (hf.comp measurable_fst))
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply hs, Measure.prod_apply (hm hs)]
  refine lintegral_congr fun x => ?_
  have hpre : Prod.mk x ⁻¹' ((fun p : A × B => (p.1, p.2 + f p.1)) ⁻¹' s)
      = (fun b => b + f x) ⁻¹' (Prod.mk x ⁻¹' s) := rfl
  rw [hpre, measure_preimage_add_right]

end PI.IwaMeasEx.MG

end
