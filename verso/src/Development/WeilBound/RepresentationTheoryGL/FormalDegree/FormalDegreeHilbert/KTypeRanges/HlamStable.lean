import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam

noncomputable section

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

A detailed English derivation is pending.
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
