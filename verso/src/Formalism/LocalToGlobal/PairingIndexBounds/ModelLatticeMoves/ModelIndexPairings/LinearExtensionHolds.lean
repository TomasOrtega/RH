import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelMoves

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

/- English proof (translation)
Introduce `k _ M T _ _ _ _ ι f g hfg`. Set `φ` to `Finsupp.linearCombination k f`. Set `ψ` to `Finsupp.linearCombination k g`. Establish `hle : LinearMap.ker φ ≤ LinearMap.ker ψ`. Introduce `c hc`.

Rewrite `hc`, the goal using `[LinearMap.mem_ker]`. Simplify using `only [φ, ψ, Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢`. Conclude with `hfg c.support c hc`. Set `φ'` to `(LinearMap.ker φ).liftQ φ le_rfl`. Set `ψ'` to `(LinearMap.ker φ).liftQ ψ hle`.

Establish `hinj : LinearMap.ker φ' = ⊥`. Apply `Submodule.ker_liftQ_eq_bot` to reduce the goal to its premises. Conclude with `le_rfl`. Take `⟨L, hL⟩` from `LinearMap.exists_leftInverse_of_injective φ' hinj`. Use `⟨ψ'.comp L, fun i => ?_⟩` and prove the remaining obligations.

Establish `hfi : f i = φ' (Submodule.Quotient.mk (Finsupp.single i 1))`. Simplify using `[φ', φ, Finsupp.linearCombination_single]`. Establish `h2 : L (φ' (Submodule.Quotient.mk (Finsupp.single i 1))) = Submodule.Quotient.mk (Finsupp.single i 1)`. Rewrite using `[← LinearMap.comp_apply, hL, LinearMap.id_apply]`. Rewrite using `[LinearMap.comp_apply, hfi, h2]`.

Simplify using `[ψ', ψ, Finsupp.linearCombination_single]`.
-/
theorem linear_extension_holds : ExtendLin := by
  intro k _ M T _ _ _ _ ι f g hfg
  classical
  let φ := Finsupp.linearCombination k f
  let ψ := Finsupp.linearCombination k g
  have hle : LinearMap.ker φ ≤ LinearMap.ker ψ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    simp only [φ, ψ, Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢
    exact hfg c.support c hc
  let φ' := (LinearMap.ker φ).liftQ φ le_rfl
  let ψ' := (LinearMap.ker φ).liftQ ψ hle
  have hinj : LinearMap.ker φ' = ⊥ := by
    apply Submodule.ker_liftQ_eq_bot
    exact le_rfl
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective φ' hinj
  refine ⟨ψ'.comp L, fun i => ?_⟩
  have hfi : f i = φ' (Submodule.Quotient.mk (Finsupp.single i 1)) := by
    simp [φ', φ, Finsupp.linearCombination_single]
  have h2 : L (φ' (Submodule.Quotient.mk (Finsupp.single i 1))) = Submodule.Quotient.mk (Finsupp.single i 1) := by
    rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
  rw [LinearMap.comp_apply, hfi, h2]
  simp [ψ', ψ, Finsupp.linearCombination_single]

end Formalism.L2.PairingIndexBounds.Mv
