import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockInvariantSubspaceEquivariantProjection
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FockProj.exists_equivariant_proj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFockInvariantSubspaceEquivariantProjection.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.fock_invariant_subspace_equivariant_projection : ∀ (p q r s : ℕ) (W : Submodule ℂ (Pol p q r s)), (∀ Z, ∀ f ∈ W, fockAct1 p q r s Z f ∈ W) → (∀ f ∈ W, ∀ n, homogeneousComponent n f ∈ W) → ∃ π : Pol p q r s →ₗ[ℂ] Pol p q r s, (∀ f, π f ∈ W) ∧ (∀ f ∈ W, π f = f) ∧ ∀ Z f, π (fockAct1 p q r s Z f) = fockAct1 p q r s Z (π f) := by
  first | exact @GlobalTheory.FockProj.exists_equivariant_proj | exact GlobalTheory.FockProj.exists_equivariant_proj | (intros; apply GlobalTheory.FockProj.exists_equivariant_proj <;> assumption)
