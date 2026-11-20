import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub

open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.WedgeNorm

/- English proof (translation)
Distinguish the cases in `hX : LinearIndependent K Xᵀ`. Take `⟨Y, hY⟩` from `h.quot κ X hX`. Take `⟨h1, h2, -⟩` from `hY κ' Z`. Rewrite using `[h1]`. Conclude with `mul_le_mul_of_nonneg_left h2 (h.nonneg κ X)`.

Establish `h0 : N (κ ⊕ κ') (fromCols X Z) = 0`. Assume the negation of the conclusion as `hne`. Establish `hli` using `(h.ne_zero _ _).1 hne`. Apply `hX` to reduce the goal to its premises. Establish `hc` using `hli.comp Sum.inl Sum.inl_injective`.

Establish `he : (((fromCols X Z)ᵀ : (κ ⊕ κ') → ι → K) ∘ Sum.inl) = (Xᵀ : κ → ι → K)`. Use function extensionality and compare the values at `i j`. Both sides reduce to the same expression. Rewrite `hc` using `[he]`. Then use the resulting hypothesis. Rewrite using `[h0]`.

Conclude with `mul_nonneg (h.nonneg _ _) (h.nonneg _ _)`.
-/
theorem wedge_fromCols_le {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] {N : Fam K ι}
    (h : IsWedge N) (κ κ' : Type) [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (X : Matrix ι κ K) (Z : Matrix ι κ' K) :
    N (κ ⊕ κ') (fromCols X Z) ≤ N κ X * N κ' Z := by
  by_cases hX : LinearIndependent K Xᵀ
  · obtain ⟨Y, hY⟩ := h.quot κ X hX
    obtain ⟨h1, h2, -⟩ := hY κ' Z
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (h.nonneg κ X)
  · have h0 : N (κ ⊕ κ') (fromCols X Z) = 0 := by
      by_contra hne
      have hli := (h.ne_zero _ _).1 hne
      apply hX
      have hc := hli.comp Sum.inl Sum.inl_injective
      have he : (((fromCols X Z)ᵀ : (κ ⊕ κ') → ι → K) ∘ Sum.inl) = (Xᵀ : κ → ι → K) := by
        funext i j
        rfl
      rwa [he] at hc
    rw [h0]
    exact mul_nonneg (h.nonneg _ _) (h.nonneg _ _)

/- English proof (translation)
Introduce `K ι _ _ _ N h κ₀ κ₁ κ₂ _ _ _ _ _ _ B A C`. Distinguish the cases in `hB : LinearIndependent K Bᵀ`. Take `⟨Y, hY⟩` from `h.quot κ₀ B hB`. Take `⟨h1, -, -⟩` from `hY (κ₁ ⊕ κ₂) (fromCols A C)`. Take `⟨h2, -, -⟩` from `hY κ₁ A`.

Take `⟨h3, -, -⟩` from `hY κ₂ C`. Rewrite using `[h1, h2, h3, Matrix.mul_fromCols]`. Establish `hle` using `wedge_fromCols_le h κ₁ κ₂ ((1 - B * Y) * A) ((1 - B * Y) * C)`. Establish `hn` using `h.nonneg κ₀ B`. Combine the equalities or inequalities in the displayed calculation.

Establish `h0 : N κ₀ B = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hB ((h.ne_zero _ _).1 hne)`. Rewrite using `[h0, mul_zero]`. Conclude with `mul_nonneg (h.nonneg _ _) (h.nonneg _ _)`.
-/
theorem wedgeSub : WedgeSub := by
  intro K ι _ _ _ N h κ₀ κ₁ κ₂ _ _ _ _ _ _ B A C
  by_cases hB : LinearIndependent K Bᵀ
  · obtain ⟨Y, hY⟩ := h.quot κ₀ B hB
    obtain ⟨h1, -, -⟩ := hY (κ₁ ⊕ κ₂) (fromCols A C)
    obtain ⟨h2, -, -⟩ := hY κ₁ A
    obtain ⟨h3, -, -⟩ := hY κ₂ C
    rw [h1, h2, h3, Matrix.mul_fromCols]
    have hle := wedge_fromCols_le h κ₁ κ₂ ((1 - B * Y) * A) ((1 - B * Y) * C)
    have hn := h.nonneg κ₀ B
    calc N κ₀ B * N (κ₁ ⊕ κ₂) (fromCols ((1 - B * Y) * A) ((1 - B * Y) * C)) * N κ₀ B
        ≤ N κ₀ B * (N κ₁ ((1 - B * Y) * A) * N κ₂ ((1 - B * Y) * C)) * N κ₀ B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hn) hn
      _ = N κ₀ B * N κ₁ ((1 - B * Y) * A) * (N κ₀ B * N κ₂ ((1 - B * Y) * C)) := by ring
  · have h0 : N κ₀ B = 0 := by
      by_contra hne
      exact hB ((h.ne_zero _ _).1 hne)
    rw [h0, mul_zero]
    exact mul_nonneg (h.nonneg _ _) (h.nonneg _ _)

end GlobalTheory.CompanionTheory.WedgeNorm
