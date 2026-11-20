import Mathlib

/- English proof (translation)
Introduce `F E _ _ _ h σ α hα x hx`. Assume the negation of the conclusion as `hxr`. Establish `hfin : FiniteDimensional F E` using `Module.finite_of_finrank_pos (by omega)`. Establish `li : LinearIndependent F ![(1 : E), x]`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `s t hst`. Establish `ht : t = 0`. Assume the negation of the conclusion as `ht`. Apply `hxr` to reduce the goal to its premises. Use `⟨-(s / t), ?_⟩` and prove the remaining obligations.

Establish `hst' : algebraMap F E s + algebraMap F E t * x = 0`. Simplify `hst` using `[Algebra.smul_def]`. Establish `ht' : algebraMap F E t ≠ 0`. Simplify using `using ht`. Rewrite using `[map_neg, map_div₀]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-hst'`. Substitute `ht` using the available equality. Simplify using `only [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst`. Conclude with `⟨by simpa using hst, rfl⟩`.

Establish `hspan : Submodule.span F (Set.range ![(1 : E), x]) = ⊤` using `li.span_eq_top_of_card_eq_finrank' (by simp [h])`. Establish `hmem : α ∈ Submodule.span F (Set.range ![(1 : E), x])`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`. Use `hα ?_` and prove the remaining obligations.

Use `clear hα`. Proceed by induction on `hmem using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨i, rfl⟩` from `hy`. Use `fin_cases i`.

Simplify using the standard rewrite rules. Simplify using `using hx`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add, ha, hb]`. Consider the case `smul c a _ ha => rw [map_smul, ha]`.
-/
theorem UpperTheory.fixed_quadratic_mem_base :
    ∀ {F E : Type} [Field F] [Field E] [Algebra F E], Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (α : E), σ α ≠ α → ∀ x, σ x = x → x ∈ (algebraMap F E).range := by
  intro F E _ _ _ h σ α hα x hx
  by_contra hxr
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have li : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hxr
      refine ⟨-(s / t), ?_⟩
      have hst' : algebraMap F E s + algebraMap F E t * x = 0 := by
        simpa [Algebra.smul_def] using hst
      have ht' : algebraMap F E t ≠ 0 := by
        simpa using ht
      rw [map_neg, map_div₀]
      field_simp
      linear_combination -hst'
    subst ht
    simp only [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
    exact ⟨by simpa using hst, rfl⟩
  have hspan : Submodule.span F (Set.range ![(1 : E), x]) = ⊤ :=
    li.span_eq_top_of_card_eq_finrank' (by simp [h])
  have hmem : α ∈ Submodule.span F (Set.range ![(1 : E), x]) := by
    rw [hspan]; exact Submodule.mem_top
  refine hα ?_
  clear hα
  induction hmem using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    fin_cases i
    · simp
    · simpa using hx
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, ha]
