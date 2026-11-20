import Mathlib

/- English proof (translation)
Introduce `H _ _ G ι _ K σ S E c hS hE`. Use `⟨{ carrier := {x : S | ∃ T : Submodule ℂ H, FiniteDimensional ℂ T ∧ (x : H) ∈ T ∧ ∀ g ∈ K, ∀ v ∈ T, σ g v ∈ T} add_mem' := ?_ zero_mem' := ?_ smul_mem' := ?_ }, fun x => Iff.rfl, ?_⟩` and prove the remaining obligations. Introduce and unpack `a b ⟨T₁, f₁, ha, h₁⟩ ⟨T₂, f₂, hb, h₂⟩`. Use `⟨T₁ ⊔ T₂, inferInstance, Submodule.add_mem_sup ha hb, ?_⟩` and prove the remaining obligations. Introduce `g hg v hv`.

Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hv`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (h₁ g hg y hy) (h₂ g hg z hz)`. Use `⟨⊥, inferInstance, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Introduce `g _ v hv`.

Rewrite using `[(Submodule.mem_bot ℂ).1 hv, map_zero]`. Conclude with `Submodule.zero_mem _`. Introduce and unpack `r x ⟨T, f, hx, h⟩`. Conclude with `⟨T, f, T.smul_mem r hx, h⟩`. Introduce and unpack `i x ⟨T, f, hx, h⟩`.

Establish `fU : FiniteDimensional ℂ (T.comap S.subtype)` using `FiniteDimensional.of_injective (S.subtype.submoduleComap T) (by`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `congrArg (fun t : T => (t : H)) hab)`.

Establish `hmem : ∀ (j : ι) (u : S), (u : H) ∈ T → ((E j u : S) : H) ∈ ⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k)` using `fun j u hu => Submodule.mem_iSup_of_mem j ⟨u, hu, rfl⟩`. Use `⟨⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k), inferInstance, hmem i x hx, ?_⟩` and prove the remaining obligations. Introduce `g hg v hv`. Establish `hle : (⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k)) ≤ (⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k)).comap (σ g)`. Use `iSup_le fun j => ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨u, hu, rfl⟩`. Rewrite using `[Submodule.mem_comap, LinearMap.comp_apply, Submodule.subtype_apply]`. Rewrite using `[hE g hg j u ⟨σ g u, hS g hg u u.2⟩ rfl]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hmem k _ (h g hg u hu))`. Conclude with `hle hv`.
-/
theorem UpperTheory.exists_invariant_subspace :
    ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (G ι : Type) [Fintype ι] (K : Set G)
        (σ : G → H →ₗ[ℂ] H) (S : Submodule ℂ H) (E : ι → Module.End ℂ S) (c : G → ι → ι → ℂ),
        (∀ g ∈ K, ∀ v ∈ S, σ g v ∈ S) →
        (∀ g ∈ K, ∀ (i : ι) (v w : S), (w : H) = σ g (v : H) →
          σ g ((E i v : S) : H) = ∑ j, c g i j • ((E j w : S) : H)) →
        ∃ V₀ : Submodule ℂ S,
          (∀ x : S, x ∈ V₀ ↔ ∃ T : Submodule ℂ H, FiniteDimensional ℂ T ∧ (x : H) ∈ T ∧
            ∀ g ∈ K, ∀ v ∈ T, σ g v ∈ T) ∧
          ∀ i, ∀ x ∈ V₀, E i x ∈ V₀ := by
  intro H _ _ G ι _ K σ S E c hS hE
  refine ⟨{ carrier := {x : S | ∃ T : Submodule ℂ H, FiniteDimensional ℂ T ∧ (x : H) ∈ T ∧
              ∀ g ∈ K, ∀ v ∈ T, σ g v ∈ T}
            add_mem' := ?_
            zero_mem' := ?_
            smul_mem' := ?_ }, fun x => Iff.rfl, ?_⟩
  · rintro a b ⟨T₁, f₁, ha, h₁⟩ ⟨T₂, f₂, hb, h₂⟩
    refine ⟨T₁ ⊔ T₂, inferInstance, Submodule.add_mem_sup ha hb, ?_⟩
    intro g hg v hv
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (h₁ g hg y hy) (h₂ g hg z hz)
  · refine ⟨⊥, inferInstance, Submodule.zero_mem _, ?_⟩
    intro g _ v hv
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]
    exact Submodule.zero_mem _
  · rintro r x ⟨T, f, hx, h⟩
    exact ⟨T, f, T.smul_mem r hx, h⟩
  · rintro i x ⟨T, f, hx, h⟩
    have fU : FiniteDimensional ℂ (T.comap S.subtype) :=
      FiniteDimensional.of_injective (S.subtype.submoduleComap T) (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun t : T => (t : H)) hab)
    have hmem : ∀ (j : ι) (u : S), (u : H) ∈ T →
        ((E j u : S) : H) ∈ ⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k) := fun j u hu =>
      Submodule.mem_iSup_of_mem j ⟨u, hu, rfl⟩
    refine ⟨⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k), inferInstance, hmem i x hx, ?_⟩
    intro g hg v hv
    have hle : (⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k)) ≤
        (⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k)).comap (σ g) := by
      refine iSup_le fun j => ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [Submodule.mem_comap, LinearMap.comp_apply, Submodule.subtype_apply]
      rw [hE g hg j u ⟨σ g u, hS g hg u u.2⟩ rfl]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (hmem k _ (h g hg u hu))
    exact hle hv
