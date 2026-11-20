import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibreSteps
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

/- English proof (translation)
Introduce `N r h g hN hg`. Take `rfl : r = N` from `le_antisymm h hN`. Use `⟨g, ?_, hg⟩` and prove the remaining obligations. Establish `hc : ∀ a : Fin r, Fin.castLE h a = a` using `fun a => Fin.ext rfl`. Establish `h1 : firstCols (1 : Matrix (Fin r) (Fin r) ℂ) r h = 1`.

Use extensionality with `p a`. Conclude with `congrArg (fun x => (1 : Matrix (Fin r) (Fin r) ℂ) p x) (hc a)`. Rewrite using `[h1, Matrix.one_mul]`. Use extensionality with `p a`. Conclude with `congrArg (fun x => g p x) (hc a)`.
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
