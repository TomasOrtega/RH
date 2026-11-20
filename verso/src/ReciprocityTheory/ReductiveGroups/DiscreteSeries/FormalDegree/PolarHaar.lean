import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarInv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarHaarA

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem muPolar_isHaar (ε : Fin n → Bool) : (muPolar ε).IsHaarMeasure := by
  haveI hR : (muPolar ε).IsMulRightInvariant := ⟨fun g => muPolar_mul_right ε g⟩
  have hinv : (muPolar ε).inv = muPolar ε := muPolar_inv ε
  haveI hL : (muPolar ε).IsMulLeftInvariant := by
    rw [← hinv]; infer_instance

  have hsurj : Function.Surjective (fdphPhi ε) := by
    intro g
    have hg : toM g ∈ UJset ε := g.2
    refine ⟨polarInv ε ⟨toM g, hg⟩, ?_⟩
    have h := fdph_toM_phi ε (polarInv ε ⟨toM g, hg⟩)
    rw [polarM_polarInv] at h
    exact Subtype.ext (Units.ext h)
  haveI hF : IsFiniteMeasureOnCompacts (muPolar ε) := by
    refine ⟨fun K hK => ?_⟩
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    rw [fdph_apply ε hKm, ← fdph_preimage]
    exact ((polarM_isClosedEmbedding ε).isCompact_preimage
      (hK.image (by fun_prop))).measure_lt_top
  haveI hO : (muPolar ε).IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    rw [fdph_apply ε hU.measurableSet]
    exact ((hU.preimage (fdph_phi_continuous ε)).measure_ne_zero _
      (hne.preimage hsurj))
  exact {}

end ReciprocityTheory.ChartRestriction.DS
