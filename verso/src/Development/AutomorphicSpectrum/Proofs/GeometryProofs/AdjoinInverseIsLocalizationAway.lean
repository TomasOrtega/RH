import Mathlib

namespace GlobalTheory.CompanionTheory.Ggeo

/- English proof (translation)
Use `letI : Algebra A S' := (Subalgebra.inclusion hle).toRingHom.toAlgebra`. Establish `hg0 : (g : Ω) ≠ 0` using `fun h => hg (Subtype.ext h)`. Establish `hinv : (g : Ω)⁻¹ ∈ S'`. Rewrite using `[hS]`. Conclude with `Algebra.subset_adjoin (Set.mem_insert _ _)`.

Establish `key : ∀ x ∈ S', ∃ (n : ℕ) (a : A), x * (g : Ω) ^ n = (a : Ω)`. Introduce `x hx`. Rewrite `hx` using `[hS]`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Break down `Set.mem_insert_iff.1 hx with rfl | hx` into its components or cases. Conclude with `⟨1, 1, by simp [hg0]⟩`. Use `⟨0, ⟨x, ?_⟩, by simp⟩` and prove the remaining obligations. Rewrite using `[hA]`. Conclude with `Algebra.subset_adjoin hx`.

Consider the case `algebraMap r => exact ⟨0, algebraMap ℚ A r, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨n, a, ha⟩` from `hx`. Take `⟨m, b, hb⟩` from `hy`. Use `⟨n + m, a * g ^ m + b * g ^ n, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Rewrite using `[← ha, ← hb]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul x y _ _ hx hy`. Take `⟨n, a, ha⟩` from `hx`.

Take `⟨m, b, hb⟩` from `hy`. Use `⟨n + m, a * b, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← ha, ← hb]`. Expand and normalize the polynomial expressions, which then agree.

Use `IsLocalization.Away.mk g ?_ ?_ ?_` and prove the remaining obligations. Use `IsUnit.of_mul_eq_one (⟨(g : Ω)⁻¹, hinv⟩ : S') ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(g : Ω) * (g : Ω)⁻¹ = 1`. Conclude with `mul_inv_cancel₀ hg0`.

Introduce `s`. Take `⟨n, a, ha⟩` from `key s s.2`. Use `⟨n, a, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(s : Ω) * (g : Ω) ^ n = (a : Ω)`.

Conclude with `ha`. Introduce `a b hab`. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `: (a : Ω) = (b : Ω)` using `congrArg (fun x : S' => (x : Ω)) hab`. Rewrite using `[Subtype.ext this]`.
-/
theorem adjoin_inv_isLocalization_away (Ω : Type) [Field Ω] [CharZero Ω] (A S' : Subalgebra ℚ Ω)
    (G : Set Ω) (hA : A = Algebra.adjoin ℚ G) (g : A) (hg : g ≠ 0)
    (hS : S' = Algebra.adjoin ℚ (insert (g : Ω)⁻¹ G)) (hle : A ≤ S') :
    @IsLocalization.Away A _ g S' _ (Subalgebra.inclusion hle).toRingHom.toAlgebra := by
  letI : Algebra A S' := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have hg0 : (g : Ω) ≠ 0 := fun h => hg (Subtype.ext h)
  have hinv : (g : Ω)⁻¹ ∈ S' := by
    rw [hS]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
  have key : ∀ x ∈ S', ∃ (n : ℕ) (a : A), x * (g : Ω) ^ n = (a : Ω) := by
    intro x hx
    rw [hS] at hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases Set.mem_insert_iff.1 hx with rfl | hx
      · exact ⟨1, 1, by simp [hg0]⟩
      · refine ⟨0, ⟨x, ?_⟩, by simp⟩
        rw [hA]; exact Algebra.subset_adjoin hx
    | algebraMap r => exact ⟨0, algebraMap ℚ A r, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, b, hb⟩ := hy
      refine ⟨n + m, a * g ^ m + b * g ^ n, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, b, hb⟩ := hy
      refine ⟨n + m, a * b, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
  refine IsLocalization.Away.mk g ?_ ?_ ?_
  · refine IsUnit.of_mul_eq_one (⟨(g : Ω)⁻¹, hinv⟩ : S') ?_
    apply Subtype.ext
    change (g : Ω) * (g : Ω)⁻¹ = 1
    exact mul_inv_cancel₀ hg0
  · intro s
    obtain ⟨n, a, ha⟩ := key s s.2
    refine ⟨n, a, ?_⟩
    apply Subtype.ext
    change (s : Ω) * (g : Ω) ^ n = (a : Ω)
    exact ha
  · intro a b hab
    refine ⟨0, ?_⟩
    have : (a : Ω) = (b : Ω) := congrArg (fun x : S' => (x : Ω)) hab
    rw [Subtype.ext this]

end GlobalTheory.CompanionTheory.Ggeo
