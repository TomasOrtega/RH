import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
open Formalism.MainNotions.N

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Assume the hypotheses and unpack their components. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isSSRep_of_isSemisimpleRing_range :
    ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k),
      IsSemisimpleRing ρ.range → IsSSRep ((ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits) := by
  intro Γ k _ _ d ρ hss W hW

  have hB : ∀ x : MonoidAlgebra k Γ, ∀ v ∈ W, (ρ x).mulVec v ∈ W := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g => intro v hv; exact hW g v hv
    | add x y hx hy =>
      intro v hv; rw [map_add, Matrix.add_mulVec]; exact W.add_mem (hx v hv) (hy v hv)
    | smul c x hx =>
      intro v hv; rw [map_smul, Matrix.smul_mulVec]; exact W.smul_mem c (hx v hv)
  let WB : Submodule ρ.range (Fin d → k) :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := by
        rintro ⟨b, x, rfl⟩ v hv
        exact hB x v hv }
  have hWB : WB.restrictScalars k = W := by ext v; rfl
  obtain ⟨WB', hc⟩ := exists_isCompl WB
  refine ⟨WB'.restrictScalars k, ?_, ?_⟩
  · intro g v hv
    have hmem : ρ (MonoidAlgebra.of k Γ g) ∈ ρ.range := ⟨_, rfl⟩
    exact WB'.smul_mem ⟨_, hmem⟩ hv
  · rw [← hWB]
    exact hc.map (Submodule.restrictScalarsLatticeHom k ρ.range (Fin d → k))

end GlobalTheory
