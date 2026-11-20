import Mathlib

/- English proof (translation)
Introduce `Λ _ _ _ N hsat`. Take `⟨k, snf⟩` from `Submodule.smithNormalForm (Module.finBasis ℤ Λ) N`. Use `⟨k, _, snf.bM, snf.f, snf.f.injective, ?_⟩` and prove the remaining obligations. Establish `ha : ∀ i, snf.a i ≠ 0`. Introduce `i h`.

Establish `h1` using `snf.snf i`. Rewrite `h1` using `[h, zero_smul]`. Conclude with `snf.bN.ne_zero i (Subtype.ext h1)`. Establish `hmem : ∀ i, snf.bM (snf.f i) ∈ N`. Introduce `i`.

Apply `hsat _ (snf.a i) (ha i)` to reduce the goal to its premises. Rewrite using `[← snf.snf i]`. Conclude with `(snf.bN i).2`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hmem i`. Introduce `x hx`. Establish `hx' : (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (Set.range snf.bN)`. Rewrite using `[snf.bN.span_eq]`.

Discharge the goal by the elementary cases of `trivial`. Use `Submodule.apply_mem_span_image_of_mem_span N.subtype hx'` as an intermediate fact. Simplify using `only [Submodule.subtype_apply] at this`. Use `Submodule.span_le.mpr ?_ this` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`.

Simplify using `only [Submodule.subtype_apply, snf.snf i]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem UpperTheory.Reformulated.B.Yha6.main :
    ∀ (Λ : Type) [inst : AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : Submodule ℤ Λ),
      (∀ (v : Λ) (n : ℤ), n ≠ (0 : ℤ) → n • v ∈ N → v ∈ N) →
        ∃ (k : ℕ) (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (f : Fin k → Fin n),
          Function.Injective f ∧ Submodule.span ℤ (Set.range fun (i : Fin k) ↦ (b : Fin n → Λ) (f i)) = N := by
  intro Λ _ _ _ N hsat
  obtain ⟨k, snf⟩ := Submodule.smithNormalForm (Module.finBasis ℤ Λ) N
  refine ⟨k, _, snf.bM, snf.f, snf.f.injective, ?_⟩
  have ha : ∀ i, snf.a i ≠ 0 := by
    intro i h
    have h1 := snf.snf i
    rw [h, zero_smul] at h1
    exact snf.bN.ne_zero i (Subtype.ext h1)
  have hmem : ∀ i, snf.bM (snf.f i) ∈ N := by
    intro i
    apply hsat _ (snf.a i) (ha i)
    rw [← snf.snf i]
    exact (snf.bN i).2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  · intro x hx
    have hx' : (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (Set.range snf.bN) := by
      rw [snf.bN.span_eq]; trivial
    have := Submodule.apply_mem_span_image_of_mem_span N.subtype hx'
    simp only [Submodule.subtype_apply] at this
    refine Submodule.span_le.mpr ?_ this
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp only [Submodule.subtype_apply, snf.snf i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
