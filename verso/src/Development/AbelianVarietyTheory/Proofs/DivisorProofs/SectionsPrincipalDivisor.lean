import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

namespace GlobalTheory

/- English proof (translation)
Use extensionality with `f`. Rewrite using `[mem_sections, Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨a, ha⟩` from `exists_fnOf_eq (U := ⊤) trivial fun x _ => (isEqn_principal g x).regularAt_iff.1 (h x)`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, algebraMap_top, ha, mul_assoc, mul_inv_cancel₀ g.ne_zero, mul_one]`. Introduce and unpack `⟨a, rfl⟩ x`. Rewrite using `[(isEqn_principal g x).regularAt_iff, Algebra.smul_def, mul_assoc, inv_mul_cancel₀ g.ne_zero, mul_one, algebraMap_top]`. Conclude with `regAt_fnOf (U := ⊤) trivial trivial a`.
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
The claim follows from `sections_principal`.
-/
example : ∀ (X : Scheme.{0}) [IsIntegral X] (g : X.functionFieldˣ),
    (principal g).sections = Submodule.span Γ(X, ⊤) {(g : X.functionField)⁻¹} := sections_principal

end GlobalTheory
