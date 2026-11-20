import Mathlib
namespace GlobalTheory.ColumnSumLemma
open Matrix
/- English proof (translation)
Use extensionality with `j`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.
-/
theorem colSum {A : Type} [CommRing A] {n r : ℕ} (C : Matrix (Fin n) (Fin r) A) (a : Fin r → A) :
    Matrix.mulVec C a = ∑ i, a i • Matrix.transpose C i := by
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/- English proof (translation)
Introduce `A _ n r C I y`. Rewrite using `[Finsupp.mem_span_image_iff_linearCombination]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, hl, rfl⟩`. Use `⟨l, fun k hk => ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Finsupp.notMem_support_iff.mp (fun h => hk (hl h))`. Rewrite using `[colSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]`. Introduce `i`. Simplify using the standard rewrite rules. Introduce and unpack `⟨a, ha, rfl⟩`.

Use `⟨Finsupp.equivFunOnFinite.symm a, fun k hk => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `(Finsupp.mem_support_iff.mp hk) (ha k h)`. Rewrite using `[colSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]`. Both sides reduce to the same expression.

Introduce `i`. Simplify using the standard rewrite rules.
-/
theorem main : ∀ {A : Type} [inst : CommRing A] {n r : ℕ} (C : Matrix (Fin n) (Fin r) A) (I : Set (Fin r)) (y : Fin n → A), y ∈ Submodule.span A ((fun (i : Fin r) ↦ Matrix.transpose C i) '' I) ↔ ∃ (a : Fin r → A), (∀ l ∉ I, a l = (0 : A)) ∧ Matrix.mulVec C a = y := by
  intro A _ n r C I y
  rw [Finsupp.mem_span_image_iff_linearCombination]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l, fun k hk => ?_, ?_⟩
    · exact Finsupp.notMem_support_iff.mp (fun h => hk (hl h))
    · rw [colSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      intro i; simp
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Finsupp.equivFunOnFinite.symm a, fun k hk => ?_, ?_⟩
    · by_contra h
      exact (Finsupp.mem_support_iff.mp hk) (ha k h)
    · rw [colSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      · rfl
      · intro i; simp
end GlobalTheory.ColumnSumLemma
