import Mathlib

/- English proof (translation)
Introduce `A F M N _ _ _ _ _ _ _ _ _ _ _ φ T y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨m, hm, rfl⟩` from `hx`. Conclude with `⟨1, one_ne_zero, m, Submodule.subset_span hm, one_smul _ _⟩`.

Consider the case `zero => exact ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by simp⟩`. Consider the case `add x z _ _ hx hz`. Take `⟨d, hd, w, hw, e⟩` from `hx`. Take `⟨d', hd', w', hw', e'⟩` from `hz`. Use `⟨d * d', mul_ne_zero hd hd', d' • w + d • w', Submodule.add_mem _ (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hw'), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm d' d]`. Consider the case `smul c x _ hx`. Take `⟨d, hd, w, hw, e⟩` from `hx`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors A) c`. Use `⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero b.2) hd, a • w, Submodule.smul_mem _ _ hw, ?_⟩` and prove the remaining obligations.

Establish `hab' : c * algebraMap A F b = algebraMap A F a` using `hab`. Rewrite using `[map_smul, ← e, ← algebraMap_smul F ((b : A) * d), ← algebraMap_smul F a, ← algebraMap_smul F d, smul_smul, smul_smul, ← hab', map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Reformulated.B.SpanImageDenominators.exists_ne_zero_smul_mem_span_image :
    ∀ {A F M N : Type} [inst : CommRing A]
    [IsDomain A] [inst_2 : Field F] [inst_3 : Algebra A F] [IsFractionRing A F] [inst_5 : AddCommGroup M]
    [inst_6 : _root_.Module A M] [inst_7 : AddCommGroup N] [inst_8 : _root_.Module A N] [inst_9 : _root_.Module F N]
    [IsScalarTower A F N] (φ : M →ₗ[A] N) (T : Set M),
    ∀ y ∈ Submodule.span F ((⇑φ : M → N) '' T),
      ∃ (d : A), d ≠ (0 : A) ∧ ∃ w ∈ Submodule.span A T, d • y = (φ : M → N) w := by
  intro A F M N _ _ _ _ _ _ _ _ _ _ _ φ T y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨1, one_ne_zero, m, Submodule.subset_span hm, one_smul _ _⟩
  | zero => exact ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨d, hd, w, hw, e⟩ := hx
    obtain ⟨d', hd', w', hw', e'⟩ := hz
    refine ⟨d * d', mul_ne_zero hd hd', d' • w + d • w',
      Submodule.add_mem _ (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hw'), ?_⟩
    rw [map_add, map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm d' d]
  | smul c x _ hx =>
    obtain ⟨d, hd, w, hw, e⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) c
    refine ⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero b.2) hd, a • w,
      Submodule.smul_mem _ _ hw, ?_⟩
    have hab' : c * algebraMap A F b = algebraMap A F a := hab
    rw [map_smul, ← e, ← algebraMap_smul F ((b : A) * d), ← algebraMap_smul F a,
      ← algebraMap_smul F d, smul_smul, smul_smul, ← hab', map_mul]
    congr 1
    ring
