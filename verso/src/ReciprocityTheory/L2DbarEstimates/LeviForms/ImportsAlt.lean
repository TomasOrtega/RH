import ReciprocityTheory.L2DbarEstimates.LeviForms.TwBound
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bergman
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem tw (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (hH : HStatement n M) (hC : HoloClosedNeed n M) :
    TWStatement n M := by
  intro X ps Ph F0 a b hps hPh hCb hlevi hF0 hF0w ha hb ha0 hb0 _ hA hB
  refine ⟨bergmanExists n M hC X ps F0 hps
    (Smooth.continuous n X.z X.isLocalHomeomorph F0 hF0).measurable hF0w, ?_⟩
  exact twBound n M hH X ps Ph F0 a b hps hPh hCb hlevi hF0 hF0w ha hb ha0 hb0 hA hB

end ReciprocityTheory.L2DbarEstimates.I
