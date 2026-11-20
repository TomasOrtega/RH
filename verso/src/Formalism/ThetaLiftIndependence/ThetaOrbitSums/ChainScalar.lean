import Formalism.ThetaLiftIndependence.Statement

namespace Formalism.ThetaLiftIndependence

namespace ChainScalarLemmas

variable {𝕜 : Type} [RCLike 𝕜] {E : ℕ → Type} [∀ j, NormedAddCommGroup (E j)]
    [∀ j, InnerProductSpace 𝕜 (E j)] [∀ j, FiniteDimensional 𝕜 (E j)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem adjoint_downChain_succ_apply (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (m : ℕ) (x : E 0) :
    LinearMap.adjoint (downChain T (m + 1)) x =
      LinearMap.adjoint (T m) (LinearMap.adjoint (downChain T m) x) := by
  show LinearMap.adjoint ((downChain T m).comp (T m)) x = _
  rw [LinearMap.adjoint_comp]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (S : ∀ j, Submodule 𝕜 (E j))
    (hS : ∀ j, ∀ x ∈ S j, LinearMap.adjoint (T j) x ∈ S (j + 1)) :
    ∀ (m : ℕ), ∀ x ∈ S 0, LinearMap.adjoint (downChain T m) x ∈ S m := by
  intro m
  induction m with
  | zero =>
    intro x hx
    show LinearMap.adjoint (LinearMap.id : E 0 →ₗ[𝕜] E 0) x ∈ S 0
    rw [LinearMap.adjoint_id]
    exact hx
  | succ m ih =>
    intro x hx
    rw [adjoint_downChain_succ_apply]
    exact hS m _ (ih x hx)

end ChainScalarLemmas

end Formalism.ThetaLiftIndependence
