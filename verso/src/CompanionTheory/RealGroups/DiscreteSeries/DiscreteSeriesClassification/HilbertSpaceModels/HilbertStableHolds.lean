import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.StepSqInt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists

noncomputable section

namespace CompanionTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Introduce `n ε lam T Ψ hP`. Establish `hv₀ : T.w ≠ 0` using `HW.KType.w_ne_zero T`. Establish `hσ` using `rreg_isURepOn ε`. Establish `hV` using `datumV_isKIrrHW hP hv₀`. Conclude with `closure_genSub_stable hσ (isDerivedOn_smE hσ) hV.1 hV.2.1 (datumV_casimir hP T.w)`.
-/
theorem hilbert_stable_holds : StepStable := by
  intro n ε lam T Ψ hP
  have hv₀ : T.w ≠ 0 := HW.KType.w_ne_zero T
  have hσ := rreg_isURepOn ε
  have hV := datumV_isKIrrHW hP hv₀
  exact closure_genSub_stable hσ (isDerivedOn_smE hσ) hV.1 hV.2.1 (datumV_casimir hP T.w)

/- English proof (translation)
Introduce `n ε lam T Ψ hP`. Establish `hv₀ : T.w ≠ 0` using `HW.KType.w_ne_zero T`. Establish `hσ` using `rreg_isURepOn ε`. Establish `hD` using `isDerivedOn_smE hσ`. Establish `hV` using `datumV_isKIrrHW hP hv₀`.

Conclude with `isKTypeOf_of_isKIrrHW hσ hD hV (datumV_kStable hP T.w) (fun μ x hx hx0 hμ => weights_le_of_irr_hw hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hx hx0 hμ)`.
-/
theorem hilbert_datum_holds : StepDatum := by
  intro n ε lam T Ψ hP
  have hv₀ : T.w ≠ 0 := HW.KType.w_ne_zero T
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV := datumV_isKIrrHW hP hv₀
  exact isKTypeOf_of_isKIrrHW hσ hD hV (datumV_kStable hP T.w) (fun μ x hx hx0 hμ =>
    weights_le_of_irr_hw hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hx hx0 hμ)

end CompanionTheory.RgDs.Hilb
