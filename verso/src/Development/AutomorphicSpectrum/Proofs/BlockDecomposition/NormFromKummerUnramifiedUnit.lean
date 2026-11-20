import Mathlib
import GroundTheory.LocalFields.MainTheorem

open ValuativeRel IntermediateField

namespace GlobalTheory.CompanionTheory.LocalField

open GroundTheory.LocalField

/- English proof (translation)
Introduce `K Ω _ _ _ _ _ _ _ N hN ξ hξ ψ hopen hψ U hU`. Establish `hgal : IsGalois K Ω` using `inferInstance`. Take `⟨hL, -⟩` from `isUnramifiedSubextension_adjoin hN hξ`. Use `hL.1` as an intermediate fact. Use `hL.isGalois` as an intermediate fact.

Establish `hclosed : IsClosed (ψ.ker : Set (Ω ≃ₐ[K] Ω))` using `Subgroup.isClosed_of_isOpen _ hopen`. Set `C : ClosedSubgroup (Ω ≃ₐ[K] Ω)` to `⟨ψ.ker, hclosed⟩`. Use `set M : IntermediateField K Ω := fixedField ψ.ker with hM`. Establish `hMU : M.fixingSubgroup = ψ.ker` using `InfiniteGalois.fixingSubgroup_fixedField C`. Establish `hML : M ≤ K⟮ξ⟯`.

Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup K⟮ξ⟯]`. Introduce `x hx`. Rewrite using `[mem_fixedField_iff]`. Introduce `g hg`. Establish `hgξ : g ξ = ξ` using `(mem_fixingSubgroup_iff _ _).1 hg ξ (mem_adjoin_simple_self K ξ)`.

Conclude with `(mem_fixedField_iff _ _).1 hx g (hψ g hgξ)`. Establish `: FiniteDimensional K M` using `FiniteDimensional.of_injective (IntermediateField.inclusion hML).toLinearMap (IntermediateField.inclusion hML).toRingHom.injective`. Establish `: IsGalois K M` using `IsGalois.of_fixedField_normal_subgroup ψ.ker`. Establish `: IsMulCommutative (M ≃ₐ[K] M)` using `⟨⟨fun τ₁ τ₂ => by`. Take `⟨g₁, rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₁`.

Take `⟨g₂, rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₂`. Rewrite using `[← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, hMU, MonoidHom.mem_ker]`. Simplify using `only [map_mul, map_inv, mul_inv_rev]`. Rewrite using `[mul_comm (ψ g₁) (ψ g₂)]`. Use the proof step `group⟩⟩`.

Establish `: IsAbelianGalois K M` using `⟨⟩`. Establish `hle` using `hL.le_maximalUnramifiedExtension`. Establish `h1` using `restrictAb_localArtinMap_of_le_maximalUnramifiedExtension K⟮ξ⟯ hle U`. Rewrite `h1` using `[hU, zpow_zero]`. Establish `h2 : restrictAb M (le_maximalAbelianExtension M) (localArtinMap K Ω U) = 1`.

Use extensionality with `x`. Establish `e1` using `restrictAb_apply M (le_maximalAbelianExtension M) (localArtinMap K Ω U) x`. Establish `e2` using `restrictAb_apply K⟮ξ⟯ (hle.trans maximalUnramifiedExtension_le_maximalAbelianExtension) (localArtinMap K Ω U) ⟨x, hML x.2⟩`. Rewrite `e2` using `[h1]`. Conclude with `e1.trans e2.symm`.

Establish `h3 : U ∈ (normUnits K M).range`. Rewrite using `[← ker_restrictAb_localArtinMap M, MonoidHom.mem_ker, MonoidHom.comp_apply]`. Conclude with `h2`. Take `⟨y, hy⟩` from `h3`. Conclude with `⟨y, by simpa using congrArg Units.val hy⟩`.
-/
theorem exists_norm_fixedField_ker_eq_unit :
    ∀ {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
      [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (N : ℕ), N ≠ 0 → ∀ ξ : Ω,
      IsPrimitiveRoot ξ (Nat.card 𝓀[K] ^ N - 1) →
      ∀ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N), IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)) →
      (∀ g : Ω ≃ₐ[K] Ω, g ξ = ξ → ψ g = 1) → ∀ U : Kˣ, GroundTheory.LocalField.ord (U : K) = 0 →
      ∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K) := by
  intro K Ω _ _ _ _ _ _ _ N hN ξ hξ ψ hopen hψ U hU
  have hgal : IsGalois K Ω := inferInstance
  obtain ⟨hL, -⟩ := isUnramifiedSubextension_adjoin hN hξ
  have := hL.1
  have := hL.isGalois
  have hclosed : IsClosed (ψ.ker : Set (Ω ≃ₐ[K] Ω)) := Subgroup.isClosed_of_isOpen _ hopen
  let C : ClosedSubgroup (Ω ≃ₐ[K] Ω) := ⟨ψ.ker, hclosed⟩
  set M : IntermediateField K Ω := fixedField ψ.ker with hM
  have hMU : M.fixingSubgroup = ψ.ker := InfiniteGalois.fixingSubgroup_fixedField C
  have hML : M ≤ K⟮ξ⟯ := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup K⟮ξ⟯]
    intro x hx
    rw [mem_fixedField_iff]
    intro g hg
    have hgξ : g ξ = ξ := (mem_fixingSubgroup_iff _ _).1 hg ξ (mem_adjoin_simple_self K ξ)
    exact (mem_fixedField_iff _ _).1 hx g (hψ g hgξ)
  have : FiniteDimensional K M := FiniteDimensional.of_injective (IntermediateField.inclusion hML).toLinearMap
    (IntermediateField.inclusion hML).toRingHom.injective
  have : IsGalois K M := IsGalois.of_fixedField_normal_subgroup ψ.ker
  have : IsMulCommutative (M ≃ₐ[K] M) := ⟨⟨fun τ₁ τ₂ => by
    obtain ⟨g₁, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₁
    obtain ⟨g₂, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₂
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker, hMU, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, mul_inv_rev]
    rw [mul_comm (ψ g₁) (ψ g₂)]
    group⟩⟩
  have : IsAbelianGalois K M := ⟨⟩
  have hle := hL.le_maximalUnramifiedExtension
  have h1 := restrictAb_localArtinMap_of_le_maximalUnramifiedExtension K⟮ξ⟯ hle U
  rw [hU, zpow_zero] at h1
  have h2 : restrictAb M (le_maximalAbelianExtension M) (localArtinMap K Ω U) = 1 := by
    ext x
    have e1 := restrictAb_apply M (le_maximalAbelianExtension M) (localArtinMap K Ω U) x
    have e2 := restrictAb_apply K⟮ξ⟯
      (hle.trans maximalUnramifiedExtension_le_maximalAbelianExtension) (localArtinMap K Ω U)
      ⟨x, hML x.2⟩
    rw [h1] at e2
    exact e1.trans e2.symm
  have h3 : U ∈ (normUnits K M).range := by
    rw [← ker_restrictAb_localArtinMap M, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact h2
  obtain ⟨y, hy⟩ := h3
  exact ⟨y, by simpa using congrArg Units.val hy⟩

end GlobalTheory.CompanionTheory.LocalField
