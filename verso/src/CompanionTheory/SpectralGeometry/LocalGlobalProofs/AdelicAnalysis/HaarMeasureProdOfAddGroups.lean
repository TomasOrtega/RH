import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.HaarTransport

/- English proof (translation)
Set `E : V ≃ₜ+ V'` to `{ e with continuous_toFun := he, continuous_invFun := hes }`. Use `haveI hH : (μ.map e).IsAddHaarMeasure := E.isAddHaarMeasure_map μ`. Establish `ha` using `Measure.isAddLeftInvariant_eq_smul (μ.map e) μ'`. Establish `ha0 : Measure.addHaarScalarFactor (μ.map e) μ' ≠ 0` using `(Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'`. Generalize the expression as in `Measure.addHaarScalarFactor (μ.map e) μ' = a at ha ha0`.

Establish `hemb : MeasurableEmbedding e` using `(Homeomorph.mk e.toEquiv he hes).measurableEmbedding`. Use `⟨⟨a, ha0, ha⟩, ?_⟩` and prove the remaining obligations. Introduce `L L' hLc hLo hLn hL hmass`. Establish `hpre : e ⁻¹' L' = L` using `by ext v; exact hL v`. Establish `hpos : μ L ≠ 0` using `(hLo.measure_pos μ hLn).ne'`.

Establish `hfin : μ L ≠ ∞` using `hLc.measure_lt_top.ne`. Establish `hLm : μ.map e L' = μ L`. Rewrite using `[hemb.map_apply, hpre]`. Establish `hval : μ L = (a : ℝ≥0∞) * μ L`. Establish `h1` using `congrArg (fun m => m L') ha`.

Simplify using `only [Measure.smul_apply, hLm] at h1`. Rewrite `h1` using `[← hmass]`. Simplify `h1` using `[ENNReal.smul_def]`. Establish `ha1 : (a : ℝ≥0∞) = 1`. Establish `h2 : (a : ℝ≥0∞) * μ L = 1 * μ L` using `by rw [one_mul]; exact hval.symm`.

Conclude with `(ENNReal.mul_left_inj hpos hfin).1 h2`. Establish `ha1' : a = 1` using `by exact_mod_cast ha1`. Rewrite using `[ha, ha1', one_smul]`.
-/
theorem map_addEquiv_haar (V V' : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [IsTopologicalAddGroup V] [AddCommGroup V'] [TopologicalSpace V'] [LocallyCompactSpace V']
    [SecondCountableTopology V'] [T2Space V'] [MeasurableSpace V'] [BorelSpace V']
    [IsTopologicalAddGroup V'] (μ : Measure V) [μ.IsAddHaarMeasure] (μ' : Measure V')
    [μ'.IsAddHaarMeasure] (e : V ≃+ V') (he : Continuous e) (hes : Continuous e.symm) :
    (∃ a : ℝ≥0, a ≠ 0 ∧ μ.map e = a • μ') ∧
      ∀ (L : Set V) (L' : Set V'), IsCompact L → IsOpen L → L.Nonempty →
        (∀ v, e v ∈ L' ↔ v ∈ L) → μ L = μ' L' → μ.map e = μ' := by
  let E : V ≃ₜ+ V' := { e with continuous_toFun := he, continuous_invFun := hes }
  haveI hH : (μ.map e).IsAddHaarMeasure := E.isAddHaarMeasure_map μ
  have ha := Measure.isAddLeftInvariant_eq_smul (μ.map e) μ'
  have ha0 : Measure.addHaarScalarFactor (μ.map e) μ' ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  generalize Measure.addHaarScalarFactor (μ.map e) μ' = a at ha ha0
  have hemb : MeasurableEmbedding e :=
    (Homeomorph.mk e.toEquiv he hes).measurableEmbedding
  refine ⟨⟨a, ha0, ha⟩, ?_⟩
  · intro L L' hLc hLo hLn hL hmass
    have hpre : e ⁻¹' L' = L := by ext v; exact hL v
    have hpos : μ L ≠ 0 := (hLo.measure_pos μ hLn).ne'
    have hfin : μ L ≠ ∞ := hLc.measure_lt_top.ne
    have hLm : μ.map e L' = μ L := by
      rw [hemb.map_apply, hpre]
    have hval : μ L = (a : ℝ≥0∞) * μ L := by
      have h1 := congrArg (fun m => m L') ha
      simp only [Measure.smul_apply, hLm] at h1
      rw [← hmass] at h1
      simpa [ENNReal.smul_def] using h1
    have ha1 : (a : ℝ≥0∞) = 1 := by
      have h2 : (a : ℝ≥0∞) * μ L = 1 * μ L := by rw [one_mul]; exact hval.symm
      exact (ENNReal.mul_left_inj hpos hfin).1 h2
    have ha1' : a = 1 := by exact_mod_cast ha1
    rw [ha, ha1', one_smul]

end GlobalTheory.CompanionTheory.SW.HaarTransport
