import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Statement
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmSubfieldsCompositumClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationPlacesCompatibleTower

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual
open scoped Pointwise

namespace GlobalTheory.QuadSplit

/- English proof (translation)
Rewrite using `[ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x`. Rewrite using `[← ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (S := A) (x := x), h]`. Both sides reduce to the same expression.

Introduce `h`. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h]`. Simplify using `[AlgEquiv.smul_def]`.
-/
theorem mem_decompositionSubgroup_iff' {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : ValuationSubring Ω)
    (g : Ω ≃ₐ[K] Ω) : g ∈ A.decompositionSubgroup K ↔ ∀ x, g x ∈ A ↔ x ∈ A := by
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  constructor
  · intro h x
    rw [← ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (S := A) (x := x), h]
    rfl
  · intro h
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h]
    simp [AlgEquiv.smul_def]

end GlobalTheory.QuadSplit
