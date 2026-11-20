import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff ContinuousMap

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem simplyConnected_cov : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {B : Set E}, SimplyConnectedSpace B → SimplyConnectedSpace (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.cov B g) := by
  intro g E _ _ B hB
  haveI : ContractibleSpace (Set.univ : Set (Fin g → ℂ)) :=
    (convex_univ (𝕜 := ℝ)).contractibleSpace ⟨0, trivial⟩
  obtain ⟨h⟩ := ContractibleSpace.hequiv_unit (Set.univ : Set (Fin g → ℂ))
  have e : (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.cov B g) ≃ₕ B :=
    (Homeomorph.Set.prod B (Set.univ : Set (Fin g → ℂ))).toHomotopyEquiv.trans
      (((ContinuousMap.HomotopyEquiv.refl B).prodCongr h).trans
        (Homeomorph.prodPUnit B).toHomotopyEquiv)
  exact e.simplyConnectedSpace

end GlobalTheory
