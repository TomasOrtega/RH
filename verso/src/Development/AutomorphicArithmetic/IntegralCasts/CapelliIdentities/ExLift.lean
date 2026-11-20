import Mathlib

/- English proof (translation)
Introduce `M Ω C _ _ _ _ _ _ _ j f`. Establish `key : ∀ x : M, f x ∈ j.fieldRange`. Introduce `x`. Establish `hx : IsIntegral ℚ x` using `Algebra.IsIntegral.isIntegral x`. Establish `hs : ((minpoly ℚ x).map (algebraMap ℚ Ω)).Splits` using `IsAlgClosed.splits _`.

Establish `hm : ((minpoly ℚ x).map (algebraMap ℚ Ω)).map j = (minpoly ℚ x).map (algebraMap ℚ C)`. Rewrite using `[Polynomial.map_map]`. Use `congr 1`. Conclude with `Subsingleton.elim _ _`. Establish `hne : ((minpoly ℚ x).map (algebraMap ℚ Ω)).map j ≠ 0`.

Rewrite using `[hm]`. Conclude with `((minpoly.monic hx).map _).ne_zero`. Establish `hr : f x ∈ (((minpoly ℚ x).map (algebraMap ℚ Ω)).map j).roots`. Rewrite using `[Polynomial.mem_roots hne, hm, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]`. Establish `h` using `Polynomial.aeval_algHom_apply f.toRatAlgHom x (minpoly ℚ x)`.

Rewrite `h` using `[minpoly.aeval, map_zero]`. Conclude with `h`. Rewrite `hr` using `[hs.roots_map, Multiset.mem_map]`. Take `⟨y, -, hy⟩` from `hr`. Conclude with `⟨y, hy⟩`.

Use `choose g hg using fun x => RingHom.mem_fieldRange.mp (key x)`. Use `⟨{ toFun := g, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hg⟩` and prove the remaining obligations. Conclude with `j.injective (by simp [hg])`. Introduce `a b`. Conclude with `j.injective (by simp [hg])`.

Conclude with `j.injective (by simp [hg])`. Introduce `a b`. Conclude with `j.injective (by simp [hg])`.
-/
theorem UpperTheory.Reformulated.B.Qj6.ex_lift :
    ∀ {M Ω C : Type} [inst : Field M] [NumberField M] [inst_2 : Field Ω]
    [CharZero Ω] [IsAlgClosed Ω] [inst_5 : Field C] [CharZero C] (j : Ω →+* C) (f : M →+* C),
    ∃ (g : M →+* Ω), ∀ (x : M), (j : Ω → C) ((g : M → Ω) x) = (f : M → C) x := by
  intro M Ω C _ _ _ _ _ _ _ j f
  have key : ∀ x : M, f x ∈ j.fieldRange := by
    intro x
    have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hs : ((minpoly ℚ x).map (algebraMap ℚ Ω)).Splits := IsAlgClosed.splits _
    have hm : ((minpoly ℚ x).map (algebraMap ℚ Ω)).map j = (minpoly ℚ x).map (algebraMap ℚ C) := by
      rw [Polynomial.map_map]
      congr 1
      exact Subsingleton.elim _ _
    have hne : ((minpoly ℚ x).map (algebraMap ℚ Ω)).map j ≠ 0 := by
      rw [hm]
      exact ((minpoly.monic hx).map _).ne_zero
    have hr : f x ∈ (((minpoly ℚ x).map (algebraMap ℚ Ω)).map j).roots := by
      rw [Polynomial.mem_roots hne, hm, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
      have h := Polynomial.aeval_algHom_apply f.toRatAlgHom x (minpoly ℚ x)
      rw [minpoly.aeval, map_zero] at h
      exact h
    rw [hs.roots_map, Multiset.mem_map] at hr
    obtain ⟨y, -, hy⟩ := hr
    exact ⟨y, hy⟩
  choose g hg using fun x => RingHom.mem_fieldRange.mp (key x)
  refine ⟨{ toFun := g, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hg⟩
  · exact j.injective (by simp [hg])
  · intro a b
    exact j.injective (by simp [hg])
  · exact j.injective (by simp [hg])
  · intro a b
    exact j.injective (by simp [hg])
