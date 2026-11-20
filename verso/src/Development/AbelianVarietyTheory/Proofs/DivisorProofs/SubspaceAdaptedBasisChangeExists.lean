import Mathlib

open Module

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ κ _ _ Y₀`. Take `⟨S, hSY, hspan, hli⟩` from `exists_linearIndependent F (Y₀ : Set (κ → F))`. Establish `hli' : LinearIndepOn F id S` using `hli`. Set `B` to `Basis.extend hli'`. Set `e` to `B.indexEquiv (Pi.basisFun F κ)`.

Set `v : κ → (κ → F)` to `fun i => ((e.symm i : _) : κ → F)`. Establish `hv : ∀ i, v i = B.reindex e i`. Introduce `i`. Simplify using `[v, B, Basis.reindex_apply, Basis.coe_extend]`. Use `⟨Matrix.of v, ?_, {i | v i ∈ S}, ?_, ?_⟩` and prove the remaining obligations.

Apply `(Matrix.isUnit_iff_isUnit_det _).mp` to reduce the goal to its premises. Apply `Matrix.linearIndependent_rows_iff_isUnit.mp` to reduce the goal to its premises. Establish `: v = ⇑(B.reindex e)` using `funext hv`. Establish `h2 : LinearIndependent F v`. Rewrite using `[this]`.

Conclude with `(B.reindex e).linearIndependent`. Conclude with `h2`. Introduce `i hi`. Conclude with `hSY hi`. Introduce `y hy`.

Establish `himg : v '' {i | v i ∈ S} = S`. Use extensionality with `x`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi, rfl⟩`.

Conclude with `hi`. Introduce `hx`. Apply the tactic sequence `refine ⟨e ⟨x, hli'.subset_extend (Set.subset_univ _) hx⟩, ?_, ?_⟩ <;> simp [v, hx]`. Establish `hy' : y ∈ Submodule.span F (v '' {i | v i ∈ S})`. Rewrite using `[himg, hspan, Submodule.span_eq]`.

Conclude with `hy`. Take `⟨l, hl, rfl⟩` from `(Finsupp.mem_span_image_iff_linearCombination F).mp hy'`. Use `⟨l, fun i hi => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hi ((Finsupp.mem_supported _ _).mp hl (Finsupp.mem_support_iff.mpr h))`.

Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]`. Use extensionality with `j`. Simplify using `[Matrix.vecMul, dotProduct, Finset.sum_apply]`.
-/
theorem exists_invertible_matrix_rows_span : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ] (Y₀ : Submodule F (κ → F)),
    ∃ P : Matrix κ κ F, IsUnit P.det ∧ ∃ s : Set κ, (∀ i ∈ s, P i ∈ Y₀) ∧
      ∀ y ∈ Y₀, ∃ c : κ → F, (∀ i ∉ s, c i = 0) ∧ y = Matrix.vecMul c P := by
  intro F _ κ _ _ Y₀
  obtain ⟨S, hSY, hspan, hli⟩ := exists_linearIndependent F (Y₀ : Set (κ → F))
  have hli' : LinearIndepOn F id S := hli
  let B := Basis.extend hli'
  let e := B.indexEquiv (Pi.basisFun F κ)
  let v : κ → (κ → F) := fun i => ((e.symm i : _) : κ → F)
  have hv : ∀ i, v i = B.reindex e i := by
    intro i; simp [v, B, Basis.reindex_apply, Basis.coe_extend]
  refine ⟨Matrix.of v, ?_, {i | v i ∈ S}, ?_, ?_⟩
  · apply (Matrix.isUnit_iff_isUnit_det _).mp
    apply Matrix.linearIndependent_rows_iff_isUnit.mp
    have : v = ⇑(B.reindex e) := funext hv
    have h2 : LinearIndependent F v := by
      rw [this]; exact (B.reindex e).linearIndependent
    exact h2
  · intro i hi; exact hSY hi
  · intro y hy
    have himg : v '' {i | v i ∈ S} = S := by
      ext x; simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hx
        refine ⟨e ⟨x, hli'.subset_extend (Set.subset_univ _) hx⟩, ?_, ?_⟩ <;> simp [v, hx]
    have hy' : y ∈ Submodule.span F (v '' {i | v i ∈ S}) := by
      rw [himg, hspan, Submodule.span_eq]; exact hy
    obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination F).mp hy'
    refine ⟨l, fun i hi => ?_, ?_⟩
    · by_contra h
      exact hi ((Finsupp.mem_supported _ _).mp hl (Finsupp.mem_support_iff.mpr h))
    · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
      ext j
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

end GlobalTheory
