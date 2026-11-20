import Mathlib

namespace FunctorialResolution.EmbeddedResolution

open Set TopologicalSpace

/- English proof (translation)
Establish `hfin : (irreducibleComponents X).Finite` using `NoetherianSpace.finite_irreducibleComponents ..`. Establish `hsub : 𝒜 ⊆ irreducibleComponents X` using `fun C hC => h𝒜 C hC`. Rewrite using `[Set.sUnion_eq_biUnion]`. Conclude with `(hfin.subset hsub).isClosed_biUnion (fun C hC => isClosed_of_mem_irreducibleComponents _ (h𝒜 C hC))`.
-/
theorem isClosed_sUnion_of_subset_irreducibleComponents {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {𝒜 : Set (Set X)} (h𝒜 : ∀ C ∈ 𝒜, C ∈ irreducibleComponents X) :
    IsClosed (⋃₀ 𝒜) := by
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents ..
  have hsub : 𝒜 ⊆ irreducibleComponents X := fun C hC => h𝒜 C hC
  rw [Set.sUnion_eq_biUnion]
  exact (hfin.subset hsub).isClosed_biUnion
    (fun C hC => isClosed_of_mem_irreducibleComponents _ (h𝒜 C hC))

/- English proof (translation)
Establish `key : (⋃₀ 𝒜)ᶜ = ⋃₀ (irreducibleComponents X \ 𝒜)`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `y hy`. Use `⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents .., ?_⟩, mem_irreducibleComponent ..⟩` and prove the remaining obligations. Introduce `hmem`.

Conclude with `hy ⟨irreducibleComponent y, hmem, mem_irreducibleComponent ..⟩`. Introduce `y hyc`. Take `⟨C, ⟨hC, hCA⟩, hyC⟩` from `hyc`. Use `show y ∉ ⋃₀ 𝒜`. Introduce `hy`.

Take `⟨D, hD, hyD⟩` from `hy`. Establish `heq : C = D` using `hsep C hC D (h𝒜 D hD) ⟨y, hyC, hyD⟩`. Rewrite `hCA` using `[heq]`. Conclude with `hCA hD`. Rewrite using `[← isClosed_compl_iff, key]`.

Conclude with `isClosed_sUnion_of_subset_irreducibleComponents (fun C hC => hC.1)`.
-/
theorem isOpen_sUnion_of_subset_irreducibleComponents {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X]
    (hsep : ∀ C₁ ∈ irreducibleComponents X, ∀ C₂ ∈ irreducibleComponents X,
      (C₁ ∩ C₂).Nonempty → C₁ = C₂)
    {𝒜 : Set (Set X)} (h𝒜 : ∀ C ∈ 𝒜, C ∈ irreducibleComponents X) :
    IsOpen (⋃₀ 𝒜) := by
  have key : (⋃₀ 𝒜)ᶜ = ⋃₀ (irreducibleComponents X \ 𝒜) := by
    apply Set.Subset.antisymm
    · intro y hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents .., ?_⟩,
        mem_irreducibleComponent ..⟩
      intro hmem
      exact hy ⟨irreducibleComponent y, hmem, mem_irreducibleComponent ..⟩
    · intro y hyc
      obtain ⟨C, ⟨hC, hCA⟩, hyC⟩ := hyc
      show y ∉ ⋃₀ 𝒜
      intro hy
      obtain ⟨D, hD, hyD⟩ := hy
      have heq : C = D := hsep C hC D (h𝒜 D hD) ⟨y, hyC, hyD⟩
      rw [heq] at hCA
      exact hCA hD
  rw [← isClosed_compl_iff, key]
  exact isClosed_sUnion_of_subset_irreducibleComponents (fun C hC => hC.1)

/- English proof (translation)
Use `hX x` as an intermediate fact. Take `⟨ξ₁, hg₁⟩` from `QuasiSober.sober h₁.1 (isClosed_of_mem_irreducibleComponents _ h₁)`. Take `⟨ξ₂, hg₂⟩` from `QuasiSober.sober h₂.1 (isClosed_of_mem_irreducibleComponents _ h₂)`. Establish `hξ₁ : closure {ξ₁} = C₁` using `hg₁`. Establish `hξ₂ : closure {ξ₂} = C₂` using `hg₂`.

Establish `hrange : Set.range (X.fromSpecStalk x).base = {y | y ⤳ x}` using `AlgebraicGeometry.Scheme.range_fromSpecStalk ..`. Establish `hm₁ : ξ₁ ∈ Set.range (X.fromSpecStalk x).base`. Rewrite using `[hrange]`. Conclude with `specializes_iff_mem_closure.mpr (by rw [hξ₁]; exact hx₁)`. Establish `hm₂ : ξ₂ ∈ Set.range (X.fromSpecStalk x).base`.

Rewrite using `[hrange]`. Conclude with `specializes_iff_mem_closure.mpr (by rw [hξ₂]; exact hx₂)`. Establish `hcont : Continuous (X.fromSpecStalk x).base` using `(X.fromSpecStalk x).continuous`. Establish `hirrU : IsIrreducible (Set.univ : Set (PrimeSpectrum (X.presheaf.stalk x)))` using `IrreducibleSpace.isIrreducible_univ ..`. Establish `himg : IsIrreducible (Set.range (X.fromSpecStalk x).base)`.

Rewrite using `[← Set.image_univ]`. Conclude with `hirrU.image _ hcont.continuousOn`. Establish `hcl : IsIrreducible (closure (Set.range (X.fromSpecStalk x).base))` using `himg.closure`. Establish `hs₁ : C₁ ⊆ closure (Set.range (X.fromSpecStalk x).base)`. Rewrite using `[← hξ₁]`.

Conclude with `closure_mono (Set.singleton_subset_iff.mpr hm₁)`. Establish `hs₂ : C₂ ⊆ closure (Set.range (X.fromSpecStalk x).base)`. Rewrite using `[← hξ₂]`. Conclude with `closure_mono (Set.singleton_subset_iff.mpr hm₂)`. Establish `e₁ : closure (Set.range (X.fromSpecStalk x).base) ⊆ C₁` using `h₁.2 hcl hs₁`.

Establish `e₂ : closure (Set.range (X.fromSpecStalk x).base) ⊆ C₂` using `h₂.2 hcl hs₂`. Conclude with `Set.Subset.antisymm (hs₁.trans e₂) (hs₂.trans e₁)`.
-/
theorem irreducibleComponents_eq_of_stalk_isDomain (X : AlgebraicGeometry.Scheme)
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) {C₁ C₂ : Set X}
    (h₁ : C₁ ∈ irreducibleComponents X) (h₂ : C₂ ∈ irreducibleComponents X)
    {x : X} (hx₁ : x ∈ C₁) (hx₂ : x ∈ C₂) : C₁ = C₂ := by
  have := hX x
  obtain ⟨ξ₁, hg₁⟩ := QuasiSober.sober h₁.1 (isClosed_of_mem_irreducibleComponents _ h₁)
  obtain ⟨ξ₂, hg₂⟩ := QuasiSober.sober h₂.1 (isClosed_of_mem_irreducibleComponents _ h₂)
  have hξ₁ : closure {ξ₁} = C₁ := hg₁
  have hξ₂ : closure {ξ₂} = C₂ := hg₂
  have hrange : Set.range (X.fromSpecStalk x).base = {y | y ⤳ x} :=
    AlgebraicGeometry.Scheme.range_fromSpecStalk ..
  have hm₁ : ξ₁ ∈ Set.range (X.fromSpecStalk x).base := by
    rw [hrange]
    exact specializes_iff_mem_closure.mpr (by rw [hξ₁]; exact hx₁)
  have hm₂ : ξ₂ ∈ Set.range (X.fromSpecStalk x).base := by
    rw [hrange]
    exact specializes_iff_mem_closure.mpr (by rw [hξ₂]; exact hx₂)
  have hcont : Continuous (X.fromSpecStalk x).base := (X.fromSpecStalk x).continuous
  have hirrU : IsIrreducible (Set.univ : Set (PrimeSpectrum (X.presheaf.stalk x))) :=
    IrreducibleSpace.isIrreducible_univ ..
  have himg : IsIrreducible (Set.range (X.fromSpecStalk x).base) := by
    rw [← Set.image_univ]
    exact hirrU.image _ hcont.continuousOn
  have hcl : IsIrreducible (closure (Set.range (X.fromSpecStalk x).base)) := himg.closure
  have hs₁ : C₁ ⊆ closure (Set.range (X.fromSpecStalk x).base) := by
    rw [← hξ₁]
    exact closure_mono (Set.singleton_subset_iff.mpr hm₁)
  have hs₂ : C₂ ⊆ closure (Set.range (X.fromSpecStalk x).base) := by
    rw [← hξ₂]
    exact closure_mono (Set.singleton_subset_iff.mpr hm₂)
  have e₁ : closure (Set.range (X.fromSpecStalk x).base) ⊆ C₁ := h₁.2 hcl hs₁
  have e₂ : closure (Set.range (X.fromSpecStalk x).base) ⊆ C₂ := h₂.2 hcl hs₂
  exact Set.Subset.antisymm (hs₁.trans e₂) (hs₂.trans e₁)

end FunctorialResolution.EmbeddedResolution
