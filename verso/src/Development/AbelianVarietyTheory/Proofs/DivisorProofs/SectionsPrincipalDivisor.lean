import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

namespace GlobalTheory

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sections_principal (X : Scheme.{0}) [IsIntegral X] (g : X.functionFieldˣ) :
    (principal g).sections = Submodule.span Γ(X, ⊤) {(g : X.functionField)⁻¹} := by
  ext f
  rw [mem_sections, Submodule.mem_span_singleton]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := exists_fnOf_eq (U := ⊤) trivial fun x _ =>
      (isEqn_principal g x).regularAt_iff.1 (h x)
    refine ⟨a, ?_⟩
    rw [Algebra.smul_def, algebraMap_top, ha, mul_assoc, mul_inv_cancel₀ g.ne_zero, mul_one]
  · rintro ⟨a, rfl⟩ x
    rw [(isEqn_principal g x).regularAt_iff, Algebra.smul_def, mul_assoc,
      inv_mul_cancel₀ g.ne_zero, mul_one, algebraMap_top]
    exact regAt_fnOf (U := ⊤) trivial trivial a

/- English proof (translation)
A detailed English derivation is pending.
-/
example : ∀ (X : Scheme.{0}) [IsIntegral X] (g : X.functionFieldˣ),
    (principal g).sections = Submodule.span Γ(X, ⊤) {(g : X.functionField)⁻¹} := sections_principal

end GlobalTheory
