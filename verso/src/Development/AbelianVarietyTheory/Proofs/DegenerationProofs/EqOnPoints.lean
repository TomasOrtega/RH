import Mathlib

open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.EqualityOnPoints

/- English proof (translation)
Use `set l := pullback.lift a b h with hl`. Establish `hcl : IsClosed (l ⁻¹' Set.range (pullback.diagonal s))` using `(pullback.diagonal s).isClosedEmbedding.isClosed_range.preimage l.continuous`. Establish `he : i ≫ l = (i ≫ a) ≫ pullback.diagonal s`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[hl, Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]`.

Rewrite using `[hl, Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id, hi]`. Establish `hsub : Set.range i ⊆ l ⁻¹' Set.range (pullback.diagonal s)`. Introduce and unpack `_ ⟨w, rfl⟩`. Use `⟨(i ≫ a) w, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← he, Scheme.Hom.comp_apply]`.

Establish `hall : l x ∈ Set.range (pullback.diagonal s)`. Establish `hcl'` using `hcl.closure_subset_iff.2 hsub`. Rewrite `hcl'` using `[i.denseRange.closure_range]`. Conclude with `hcl' (Set.mem_univ x)`. Take `⟨y, hy⟩` from `hall`.

Establish `ha : a x = y`. Establish `e : (pullback.diagonal s ≫ pullback.fst s s) y = (l ≫ pullback.fst s s) x`. Rewrite using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]`. Rewrite `e` using `[pullback.diagonal_fst, hl, pullback.lift_fst]`. Simplify using `using e.symm`.

Establish `hb : b x = y`. Establish `e : (pullback.diagonal s ≫ pullback.snd s s) y = (l ≫ pullback.snd s s) x`. Rewrite using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]`. Rewrite `e` using `[pullback.diagonal_snd, hl, pullback.lift_snd]`. Simplify using `using e.symm`.

Rewrite using `[ha, hb]`.
-/
theorem eq_on_points {W X Y Z : Scheme.{0}} {a b : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : a ≫ s = b ≫ s) (i : W ⟶ X) [IsDominant i] (hi : i ≫ a = i ≫ b) (x : X) :
    (a x : Y) = b x := by

  set l := pullback.lift a b h with hl
  have hcl : IsClosed (l ⁻¹' Set.range (pullback.diagonal s)) :=
    (pullback.diagonal s).isClosedEmbedding.isClosed_range.preimage l.continuous

  have he : i ≫ l = (i ≫ a) ≫ pullback.diagonal s := by
    apply pullback.hom_ext
    · rw [hl, Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
    · rw [hl, Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
        Category.comp_id, hi]
  have hsub : Set.range i ⊆ l ⁻¹' Set.range (pullback.diagonal s) := by
    rintro _ ⟨w, rfl⟩
    refine ⟨(i ≫ a) w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← he, Scheme.Hom.comp_apply]

  have hall : l x ∈ Set.range (pullback.diagonal s) := by
    have hcl' := hcl.closure_subset_iff.2 hsub
    rw [i.denseRange.closure_range] at hcl'
    exact hcl' (Set.mem_univ x)
  obtain ⟨y, hy⟩ := hall
  have ha : a x = y := by
    have e : (pullback.diagonal s ≫ pullback.fst s s) y = (l ≫ pullback.fst s s) x := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
    rw [pullback.diagonal_fst, hl, pullback.lift_fst] at e
    simpa using e.symm
  have hb : b x = y := by
    have e : (pullback.diagonal s ≫ pullback.snd s s) y = (l ≫ pullback.snd s s) x := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
    rw [pullback.diagonal_snd, hl, pullback.lift_snd] at e
    simpa using e.symm
  rw [ha, hb]

end GlobalTheory.EqualityOnPoints
