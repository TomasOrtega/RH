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
Introduce `δ hδ`. Rewrite `hδ`, the goal using `[MulAction.mem_stabilizer_iff]`. Rewrite using `[← smul_pt, hδ]`.
-/
theorem stabilizer_le_pt (p : ConjPair H X) :
    MulAction.stabilizer H p ≤ MulAction.stabilizer H p.pt := by
  intro δ hδ
  rw [MulAction.mem_stabilizer_iff] at hδ ⊢
  rw [← smul_pt, hδ]

/- English proof (translation)
Rewrite using `[MulAction.mem_stabilizer_iff, ConjPair.ext_iff, smul_elt, smul_pt]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨?_, h2⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨?_, h2⟩` and prove the remaining obligations. Rewrite using `[h1]`. Use `group`.
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
