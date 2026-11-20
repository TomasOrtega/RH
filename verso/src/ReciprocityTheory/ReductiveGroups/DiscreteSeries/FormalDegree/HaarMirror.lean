import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarHaar

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Unfold `cPQ`. Check the signs of the components of the expression.
-/
theorem cPQ_pos (ε : Fin n → Bool) : 0 < cPQ ε := by
  unfold cPQ
  positivity

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem real_UJ_eq_UJ (ε : Fin n → Bool) : Formalism.REAL.UJ ε = UJ ε := by
  rfl

/- English proof (translation)
Introduce `H hH`. Substitute `hH` using the available equality. Establish `key` using `muPolar_isHaar ε`. Establish `h0 : (inferInstance : MeasurableSpace (UJ ε)) = borel (UJ ε)` using `BorelSpace.measurable_eq`. Introduce `m hm`.

Establish `h1 : m = borel (UJ ε)` using `hm.measurable_eq`. Establish `e : m = _` using `h1.trans h0.symm`. Substitute `e` using the available equality. Conclude with `key`.
-/
theorem comap_muPolarMat_isHaar (ε : Fin n → Bool) :
    ∀ (H : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ), H = UJ ε → ∀ (m : MeasurableSpace H), @BorelSpace H _ m →
      (Measure.comap (β := Fin n → Fin n → ℂ)
        (fun g : H => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
        (muPolarMat ε)).IsHaarMeasure := by
  intro H hH
  subst hH
  have key := muPolar_isHaar ε
  have h0 : (inferInstance : MeasurableSpace (UJ ε)) = borel (UJ ε) := BorelSpace.measurable_eq
  intro m hm
  have h1 : m = borel (UJ ε) := hm.measurable_eq
  have e : m = _ := h1.trans h0.symm
  subst e
  exact key

/- English proof (translation)
Use `haveI hH := comap_muPolarMat_isHaar ε (Formalism.REAL.UJ ε) (real_UJ_eq_UJ ε) inferInstance inferInstance`. Unfold `muCD`. Establish `hc : ENNReal.ofReal (cPQ ε) ≠ 0` using `(ENNReal.ofReal_pos.mpr (cPQ_pos ε)).ne'`. Establish `ht : ENNReal.ofReal (cPQ ε) ≠ ⊤` using `ENNReal.ofReal_ne_top`. Conclude with `MeasureTheory.Measure.IsHaarMeasure.smul _ hc ht`.
-/
theorem muCD_isHaar (ε : Fin n → Bool) : (muCD ε).IsHaarMeasure := by

  haveI hH := comap_muPolarMat_isHaar ε (Formalism.REAL.UJ ε) (real_UJ_eq_UJ ε) inferInstance inferInstance
  unfold muCD
  have hc : ENNReal.ofReal (cPQ ε) ≠ 0 := (ENNReal.ofReal_pos.mpr (cPQ_pos ε)).ne'
  have ht : ENNReal.ofReal (cPQ ε) ≠ ⊤ := ENNReal.ofReal_ne_top
  exact MeasureTheory.Measure.IsHaarMeasure.smul _ hc ht

end ReciprocityTheory.ChartRestriction.DS
