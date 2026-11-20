import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.ModuLR

/- English proof (translation)
Use `set μ₁ : Measure G₁ := Measure.addHaar`. Use `set μ₂ : Measure G₂ := Measure.addHaar`. Use `set μ : Measure (G₁ × G₂) := μ₁.prod μ₂`. Establish `hμ : μ.IsAddHaarMeasure` using `by infer_instance`. Establish `hreg : μ.Regular` using `by infer_instance`.

Use `set φ := prodCE e₁ e₂`. Establish `h1` using `addEquivAddHaarChar_smul_map μ₁ e₁`. Establish `h2` using `addEquivAddHaarChar_smul_map μ₂ e₂`. Establish `h` using `addEquivAddHaarChar_smul_map μ φ`. Establish `hm1 : (μ₁.map e₁).IsAddHaarMeasure` using `e₁.isAddHaarMeasure_map μ₁`.

Establish `hm2 : (μ₂.map e₂).IsAddHaarMeasure` using `e₂.isAddHaarMeasure_map μ₂`. Establish `hmap : μ.map φ = (μ₁.map e₁).prod (μ₂.map e₂)`. Use `Measure.map_prod_map μ₁ μ₂ e₁.continuous.measurable e₂.continuous.measurable` as an intermediate fact. Conclude with `this.symm`. Establish `hc : (addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂) • μ.map φ = μ`.

Rewrite using `[hmap]`. Use `conv_rhs => rw [show μ = μ₁.prod μ₂ from rfl, ← h1, ← h2]`. Rewrite using `[mul_smul]`. Rewrite using `[Measure.prod_smul_left, Measure.prod_smul_right]`. Establish `hν : (μ.map φ).IsAddHaarMeasure` using `φ.isAddHaarMeasure_map μ`.

Take `⟨K, hK, hK0⟩` from `exists_compact_mem_nhds (0 : G₁ × G₂)`. Establish `hpos : (μ.map φ) K ≠ 0` using `(Measure.measure_pos_of_mem_nhds _ hK0).ne'`. Establish `hfin : (μ.map φ) K ≠ ∞` using `hK.measure_lt_top.ne`. Establish `key` using `congrArg (fun m : Measure (G₁ × G₂) => m K) (h.trans hc.symm)`. Simplify using `only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at key`.

Use `(ENNReal.mul_left_inj hpos hfin).1 key` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem addEquivAddHaarChar_prodCE (G₁ G₂ : Type) [AddCommGroup G₁] [TopologicalSpace G₁]
    [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁]
    [MeasurableSpace G₁] [BorelSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂]
    [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂] [SecondCountableTopology G₂]
    [MeasurableSpace G₂] [BorelSpace G₂] (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂) :
    addEquivAddHaarChar (prodCE e₁ e₂) = addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂ := by
  set μ₁ : Measure G₁ := Measure.addHaar
  set μ₂ : Measure G₂ := Measure.addHaar
  set μ : Measure (G₁ × G₂) := μ₁.prod μ₂
  have hμ : μ.IsAddHaarMeasure := by infer_instance
  have hreg : μ.Regular := by infer_instance
  set φ := prodCE e₁ e₂
  have h1 := addEquivAddHaarChar_smul_map μ₁ e₁
  have h2 := addEquivAddHaarChar_smul_map μ₂ e₂
  have h := addEquivAddHaarChar_smul_map μ φ
  have hm1 : (μ₁.map e₁).IsAddHaarMeasure := e₁.isAddHaarMeasure_map μ₁
  have hm2 : (μ₂.map e₂).IsAddHaarMeasure := e₂.isAddHaarMeasure_map μ₂
  have hmap : μ.map φ = (μ₁.map e₁).prod (μ₂.map e₂) := by
    have := Measure.map_prod_map μ₁ μ₂ e₁.continuous.measurable e₂.continuous.measurable
    exact this.symm
  have hc : (addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂) • μ.map φ = μ := by
    rw [hmap]
    conv_rhs => rw [show μ = μ₁.prod μ₂ from rfl, ← h1, ← h2]
    rw [mul_smul]
    rw [Measure.prod_smul_left, Measure.prod_smul_right]
  have hν : (μ.map φ).IsAddHaarMeasure := φ.isAddHaarMeasure_map μ
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G₁ × G₂)
  have hpos : (μ.map φ) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hfin : (μ.map φ) K ≠ ∞ := hK.measure_lt_top.ne
  have key := congrArg (fun m : Measure (G₁ × G₂) => m K) (h.trans hc.symm)
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at key
  have := (ENNReal.mul_left_inj hpos hfin).1 key
  exact_mod_cast this

end GlobalTheory.ModuLR
