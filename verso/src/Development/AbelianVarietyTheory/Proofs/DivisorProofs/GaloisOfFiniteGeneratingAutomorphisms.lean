import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `K K' _ _ i hfin Γ _ s hs hfix`. Use `letI := i.toAlgebra`. Use `haveI : FiniteDimensional K K' := hfin`. Set `t : Γ → (K' ≃ₐ[K] K')` to `fun g => AlgEquiv.ofRingEquiv (f := s g) (hs g)`. Set `H : Subgroup (K' ≃ₐ[K] K')` to `Subgroup.closure (Set.range t)`.

Establish `hH : IntermediateField.fixedField H = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Establish `h1 : ∀ g, s g y = y` using `fun g => hy ⟨t g, Subgroup.subset_closure ⟨g, rfl⟩⟩`. Take `⟨x, rfl⟩` from `hfix y h1`.

Conclude with `IntermediateField.algebraMap_mem _ x`. Establish `hG : IsGalois K K'`. Apply `IsGalois.of_fixedField_eq_bot` to reduce the goal to its premises. Rewrite using `[eq_bot_iff, ← hH]`. Conclude with `IntermediateField.fixedField_le le_top`.

Use `⟨hG, ?_⟩` and prove the remaining obligations. Introduce `σ hσ`. Establish `hHtop : H = ⊤`. Rewrite using `[← IntermediateField.fixingSubgroup_fixedField H, hH, IntermediateField.fixingSubgroup_bot]`. Set `σ' : K' ≃ₐ[K] K'` to `AlgEquiv.ofRingEquiv (f := σ) hσ`.

Establish `hmem : σ' ∈ Submonoid.closure (Set.range t)`. Rewrite using `[← Subgroup.closure_toSubmonoid_of_finite]`. Use `show σ' ∈ H`. Rewrite using `[hHtop]`. Conclude with `Subgroup.mem_top _`.

Set `φ : (K' ≃ₐ[K] K') →* (K' ≃+* K')` to `{ toFun := fun τ => τ.toRingEquiv map_one' := rfl map_mul' := fun _ _ => rfl }`. Establish `hmap` using `Submonoid.mem_map_of_mem φ hmem`. Rewrite `hmap` using `[MonoidHom.map_mclosure, ← Set.range_comp]`. Establish `hc : (φ ∘ t) = s`. Use function extensionality and compare the values at `g`.

Use extensionality with `y`. Both sides reduce to the same expression. Establish `hσ' : φ σ' = σ` using `by ext y; rfl`. Rewrite `hmap` using `[hc, hσ']`. Then use the resulting hypothesis.
-/
theorem galois_of_finite_generating_automorphisms : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → (letI := i.toAlgebra; IsGalois K K') ∧ ∀ σ : K' ≃+* K', (∀ x, σ (i x) = i x) → σ ∈ Submonoid.closure (Set.range s) := by
  intro K K' _ _ i hfin Γ _ s hs hfix
  letI := i.toAlgebra
  haveI : FiniteDimensional K K' := hfin
  let t : Γ → (K' ≃ₐ[K] K') := fun g => AlgEquiv.ofRingEquiv (f := s g) (hs g)
  let H : Subgroup (K' ≃ₐ[K] K') := Subgroup.closure (Set.range t)
  have hH : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h1 : ∀ g, s g y = y := fun g => hy ⟨t g, Subgroup.subset_closure ⟨g, rfl⟩⟩
    obtain ⟨x, rfl⟩ := hfix y h1
    exact IntermediateField.algebraMap_mem _ x
  have hG : IsGalois K K' := by
    apply IsGalois.of_fixedField_eq_bot
    rw [eq_bot_iff, ← hH]
    exact IntermediateField.fixedField_le le_top
  refine ⟨hG, ?_⟩
  intro σ hσ
  have hHtop : H = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, hH, IntermediateField.fixingSubgroup_bot]
  let σ' : K' ≃ₐ[K] K' := AlgEquiv.ofRingEquiv (f := σ) hσ
  have hmem : σ' ∈ Submonoid.closure (Set.range t) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    show σ' ∈ H
    rw [hHtop]; exact Subgroup.mem_top _
  let φ : (K' ≃ₐ[K] K') →* (K' ≃+* K') :=
    { toFun := fun τ => τ.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hmap := Submonoid.mem_map_of_mem φ hmem
  rw [MonoidHom.map_mclosure, ← Set.range_comp] at hmap
  have hc : (φ ∘ t) = s := by
    funext g; ext y; rfl
  have hσ' : φ σ' = σ := by ext y; rfl
  rwa [hc, hσ'] at hmap

end GlobalTheory
