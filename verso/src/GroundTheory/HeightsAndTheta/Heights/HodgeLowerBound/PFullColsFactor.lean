import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibreSteps
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem FullColsFactor.proof : FullColsFactor.Statement := by
  intro N r h g hN hg
  obtain rfl : r = N := le_antisymm h hN
  refine ⟨g, ?_, hg⟩
  have hc : ∀ a : Fin r, Fin.castLE h a = a := fun a => Fin.ext rfl
  have h1 : firstCols (1 : Matrix (Fin r) (Fin r) ℂ) r h = 1 := by
    ext p a
    exact congrArg (fun x => (1 : Matrix (Fin r) (Fin r) ℂ) p x) (hc a)
  rw [h1, Matrix.one_mul]
  ext p a
  exact congrArg (fun x => g p x) (hc a)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
