import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LaurentDegenerationFirstOrderKernel
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.laurent_degeneration` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLaurentDegenerationFirstOrderKernel.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.laurent_degeneration_first_order_kernel : ∀ (k : Type) [Field k], ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ : K), ∀ (a e : ℕ) (V : Submodule k (Fin a → k)) (U : Type) [AddCommGroup U] [Module k U] (t u : V →ₗ[k] U), e ≤ 1 → (∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → ∀ y : Fin (e + 1) → Fin a → K, (∀ j (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (y j c)) ∧ (∀ c, x'.1 c = π (σ * y j c)) ∧ t x = u x') → ¬ LinearIndependent K y := by
  first | exact @GlobalTheory.laurent_degeneration | exact GlobalTheory.laurent_degeneration | (intros; apply GlobalTheory.laurent_degeneration <;> assumption)
