import Mathlib

namespace PositivityTheory.SiegelWeilFormula.KWhit.MeasG

open MeasureTheory

/- English proof (translation)
Establish `e : μ' = Measure.addHaarScalarFactor μ' μ • μ` using `Measure.isAddLeftInvariant_eq_smul μ' μ`. Establish `h'' : IsAddFundamentalDomain Γ 𝓕' μ` using `h'.mono (Measure.absolutelyContinuous_isAddHaarMeasure μ μ')`. Establish `hm : μ 𝓕' = μ 𝓕` using `h''.measure_eq h`. Establish `hc : (Measure.addHaarScalarFactor μ' μ : ENNReal) = 1`. Use `h1'` as an intermediate fact.

Rewrite `this` using `[e, Measure.smul_apply, hm, h1, ENNReal.smul_def, smul_eq_mul, mul_one]`. Conclude with `this`. Establish `hc' : Measure.addHaarScalarFactor μ' μ = 1` using `by exact_mod_cast hc`. Rewrite using `[e, hc', one_smul]`.
-/
theorem covol_unique {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ]
    {μ μ' : Measure G} [μ.IsAddHaarMeasure] [μ'.IsAddHaarMeasure] {𝓕 𝓕' : Set G}
    (h : IsAddFundamentalDomain Γ 𝓕 μ) (h' : IsAddFundamentalDomain Γ 𝓕' μ') (h1 : μ 𝓕 = 1) (h1' : μ' 𝓕' = 1) :
    μ' = μ := by
  have e : μ' = Measure.addHaarScalarFactor μ' μ • μ := Measure.isAddLeftInvariant_eq_smul μ' μ
  have h'' : IsAddFundamentalDomain Γ 𝓕' μ := h'.mono (Measure.absolutelyContinuous_isAddHaarMeasure μ μ')
  have hm : μ 𝓕' = μ 𝓕 := h''.measure_eq h
  have hc : (Measure.addHaarScalarFactor μ' μ : ENNReal) = 1 := by
    have := h1'
    rw [e, Measure.smul_apply, hm, h1, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact this
  have hc' : Measure.addHaarScalarFactor μ' μ = 1 := by exact_mod_cast hc
  rw [e, hc', one_smul]

end PositivityTheory.SiegelWeilFormula.KWhit.MeasG
