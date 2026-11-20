import Mathlib

namespace GlobalTheory.MassConj

@[ext]
structure ConjPair (H X : Type) where

  elt : H

  pt : X

variable {H X : Type} [Group H] [MulAction H X]

instance : MulAction H (ConjPair H X) where
  smul δ p := ⟨δ * p.elt * δ⁻¹, δ • p.pt⟩
  one_smul p := by
    show ConjPair.mk _ _ = p
    ext <;> simp
  mul_smul δ ε p := by
    show ConjPair.mk (δ * ε * p.elt * (δ * ε)⁻¹) ((δ * ε) • p.pt) =
      ConjPair.mk (δ * (ε * p.elt * ε⁻¹) * δ⁻¹) (δ • ε • p.pt)
    ext
    · simp only; group
    · exact mul_smul δ ε p.pt

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem smul_elt (δ : H) (p : ConjPair H X) : (δ • p).elt = δ * p.elt * δ⁻¹ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem smul_pt (δ : H) (p : ConjPair H X) : (δ • p).pt = δ • p.pt := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem stabilizer_le_pt (p : ConjPair H X) :
    MulAction.stabilizer H p ≤ MulAction.stabilizer H p.pt := by
  intro δ hδ
  rw [MulAction.mem_stabilizer_iff] at hδ ⊢
  rw [← smul_pt, hδ]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_stabilizer_iff (δ : H) (p : ConjPair H X) :
    δ ∈ MulAction.stabilizer H p ↔ δ * p.elt = p.elt * δ ∧ δ • p.pt = p.pt := by
  rw [MulAction.mem_stabilizer_iff, ConjPair.ext_iff, smul_elt, smul_pt]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    calc δ * p.elt = δ * p.elt * δ⁻¹ * δ := by group
      _ = p.elt * δ := by rw [h1]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1]; group

end GlobalTheory.MassConj
