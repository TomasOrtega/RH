import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsIntValuationLtOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. A detailed English derivation is pending.
-/
theorem RegularityIntegral.proof (hC : RegularityValuationCentre.Statement) (hB : RegularityRelativeClosedPoint.Statement) :
    RegularityIntegral.Statement := by
  intro K _ ι _ P hP x
  obtain ⟨hF, hNF⟩ := RegularityFunctionFieldNumber.proof K ι P hP
  let _ := hF.toField
  have hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers (funField P)),
      v.valuation (funField P) (x : funField P) ≤ 1 := by
    intro v
    obtain ⟨n, hn0, hn⟩ := RegularityValuationCentre.exists_int_valuation_lt_one v
    obtain ⟨W, hW, hPW, hnW, hsub⟩ := hC K ι P hP.2.1 _ (v.valuation (funField P)) n hn
    have hWP : W ≠ P := by
      rintro rfl
      have h0 : n ∈ W.comap (C : ℤ →+* MRing ι) := hnW
      rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1, Ideal.mem_bot] at h0
      exact hn0 h0
    exact hsub x (x.2 W (hB K ι P W hP hW hPW hWP) hPW)
  obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (funField P)
    (x : funField P) hv
  have hint : IsIntegral ℤ (x : funField P) := hy ▸ (Algebra.IsIntegral.isIntegral y).algebraMap
  let f : funField P →ₐ[ℤ] FractionRing (MRing ι ⧸ P) :=
    { (funField P).subtype with commutes' := fun n => by simp }
  exact hint.map f

end

end GroundTheory.Heights₂.Heights.Inter
