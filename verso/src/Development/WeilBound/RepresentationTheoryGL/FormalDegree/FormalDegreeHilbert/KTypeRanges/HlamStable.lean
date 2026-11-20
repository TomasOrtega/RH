import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam

noncomputable section

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

/- English proof (translation)
Introduce `n ε lam T Ψ hP g hg x hx`. Establish `hw : T.w ≠ 0` using `fun h => by`. Establish `h1` using `T.w_norm`. Rewrite `h1` using `[h, norm_zero]`. Conclude with `zero_ne_one h1`.

Establish `hK` using `datumV_isKIrrHW hP hw`. Conclude with `closure_genSub_stable (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε)) hK.1 hK.2.1 (datumV_casimir hP T.w) g hg x hx`.
-/
theorem hlamStable : HlamStable := by
  intro n ε lam T Ψ hP g hg x hx
  have hw : T.w ≠ 0 := fun h => by
    have h1 := T.w_norm
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hK := datumV_isKIrrHW hP hw
  exact closure_genSub_stable (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε)) hK.1 hK.2.1
    (datumV_casimir hP T.w) g hg x hx

end PositivityTheory.RgFd
