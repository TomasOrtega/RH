import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `X' Y' i₁ i₂ f' H`. Establish `c₁` using `h₁.universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ g₁).paste_horiz H)`. Establish `c₂` using `h₂.universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ g₂).paste_horiz H)`. Introduce `Zs hZ`.

Establish `e : f' '' Zs = (pullback.fst i₁ g₁ ≫ f') '' (pullback.fst i₁ g₁ ⁻¹' Zs) ∪ (pullback.fst i₁ g₂ ≫ f') '' (pullback.fst i₁ g₂ ⁻¹' Zs)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Break down `hcov (i₁ x) with ⟨a, ha⟩ | ⟨a, ha⟩` into its components or cases. Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback x a ha.symm`.

Conclude with `Or.inl ⟨z, by simpa [hz] using hx, by simp [hz]⟩`. Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback x a ha.symm`. Conclude with `Or.inr ⟨z, by simpa [hz] using hx, by simp [hz]⟩`. Apply the tactic sequence `rintro _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) <;> exact ⟨_, hz, by simp⟩`. Rewrite using `[e]`.

Conclude with `(c₁ _ (hZ.preimage (Scheme.Hom.continuous _))).union (c₂ _ (hZ.preimage (Scheme.Hom.continuous _)))`.
-/
theorem universallyClosed_of_jointly_surjective {A₁ A₂ X Z : Scheme.{0}} (g₁ : A₁ ⟶ X)
    (g₂ : A₂ ⟶ X) (k : X ⟶ Z) (hcov : ∀ x : X, (∃ a, g₁ a = x) ∨ ∃ a, g₂ a = x)
    (h₁ : UniversallyClosed (g₁ ≫ k)) (h₂ : UniversallyClosed (g₂ ≫ k)) :
    UniversallyClosed k := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have c₁ := h₁.universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ g₁).paste_horiz H)
  have c₂ := h₂.universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ g₂).paste_horiz H)
  intro Zs hZ
  have e : f' '' Zs = (pullback.fst i₁ g₁ ≫ f') '' (pullback.fst i₁ g₁ ⁻¹' Zs) ∪
      (pullback.fst i₁ g₂ ≫ f') '' (pullback.fst i₁ g₂ ⁻¹' Zs) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rcases hcov (i₁ x) with ⟨a, ha⟩ | ⟨a, ha⟩
      · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
        exact Or.inl ⟨z, by simpa [hz] using hx, by simp [hz]⟩
      · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
        exact Or.inr ⟨z, by simpa [hz] using hx, by simp [hz]⟩
    · rintro _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) <;> exact ⟨_, hz, by simp⟩
  rw [e]
  exact (c₁ _ (hZ.preimage (Scheme.Hom.continuous _))).union
    (c₂ _ (hZ.preimage (Scheme.Hom.continuous _)))

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `S W W' f π hsep hlft T' T'' h₁ h₂`. Establish `hle₁ : T'.map π ⊓ T'' ≤ T'.map π` using `inf_le_left`. Establish `hle₂ : T'.map π ⊓ T'' ≤ T''` using `inf_le_right`. Set `g₁` to `Scheme.IdealSheafData.subschemeMap T' (T'.map π ⊓ T'') π hle₁`. Set `g₂` to `Scheme.IdealSheafData.inclusion hle₂`.

Establish `e₁ : g₁ ≫ (T'.map π ⊓ T'').subschemeι ≫ f = T'.subschemeι ≫ π ≫ f` using `by simp [g₁]`. Establish `e₂ : g₂ ≫ (T'.map π ⊓ T'').subschemeι ≫ f = T''.subschemeι ≫ f` using `by simp [g₂]`. Establish `huc₀ : UniversallyClosed ((T'.subschemeι ≫ π) ≫ f)`. Rewrite using `[Category.assoc]`. Use `infer_instance`.

Establish `huc : UniversallyClosed (T'.subschemeι ≫ π)` using `UniversallyClosed.of_comp_of_isSeparated _ f`. Establish `hsupp : ((T'.map π).support : Set W) = Set.range (T'.subschemeι ≫ π)`. Rewrite using `[Scheme.IdealSheafData.map, Scheme.Hom.support_ker]`. Conclude with `(T'.subschemeι ≫ π).isClosedMap.isClosed_range.closure_eq`. Establish `hmul : T'.map π * T'' ≤ T'.map π ⊓ T''`.

Introduce `U`. Conclude with `Ideal.mul_le_inf`. Establish `hcov : ∀ x : (T'.map π ⊓ T'').subscheme, (∃ a, g₁ a = x) ∨ ∃ a, g₂ a = x`. Introduce `x`. Establish `hx : (T'.map π ⊓ T'').subschemeι x ∈ (T'.map π ⊓ T'').support`.

Rewrite using `[← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]`. Conclude with `⟨x, rfl⟩`. Establish `hx'` using `Scheme.IdealSheafData.support_antitone hmul hx`. Rewrite `hx'` using `[Scheme.IdealSheafData.support_mul]`. Establish `hinj` using `(T'.map π ⊓ T'').subschemeι.isClosedEmbedding.injective`.

Break down `hx' with hx' | hx'` into its components or cases. Rewrite `hx'` using `[hsupp]`. Take `⟨a, ha⟩` from `hx'`. Use `Or.inl ⟨a, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[← ha, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.subschemeMap_subschemeι]`.

Rewrite `hx'` using `[← Scheme.IdealSheafData.range_subschemeι]`. Take `⟨a, ha⟩` from `hx'`. Use `Or.inr ⟨a, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[← ha, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι]`. Establish `huc' : UniversallyClosed ((T'.map π ⊓ T'').subschemeι ≫ f)` using `universallyClosed_of_jointly_surjective g₁ g₂ _ hcov (e₁ ▸ inferInstance) (e₂ ▸ inferInstance)`.

Conclude with `{ }`.
-/
theorem isProper_map_inf_subschemeι : ∀ (S W W' : Scheme.{0}) (f : W ⟶ S) (π : W' ⟶ W),
    IsSeparated f → LocallyOfFiniteType f → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData),
    IsProper (T'.subschemeι ≫ π ≫ f) → IsProper (T''.subschemeι ≫ f) →
    IsProper ((T'.map π ⊓ T'').subschemeι ≫ f) := by
  intro S W W' f π hsep hlft T' T'' h₁ h₂
  have hle₁ : T'.map π ⊓ T'' ≤ T'.map π := inf_le_left
  have hle₂ : T'.map π ⊓ T'' ≤ T'' := inf_le_right
  let g₁ := Scheme.IdealSheafData.subschemeMap T' (T'.map π ⊓ T'') π hle₁
  let g₂ := Scheme.IdealSheafData.inclusion hle₂
  have e₁ : g₁ ≫ (T'.map π ⊓ T'').subschemeι ≫ f = T'.subschemeι ≫ π ≫ f := by simp [g₁]
  have e₂ : g₂ ≫ (T'.map π ⊓ T'').subschemeι ≫ f = T''.subschemeι ≫ f := by simp [g₂]
  have huc₀ : UniversallyClosed ((T'.subschemeι ≫ π) ≫ f) := by
    rw [Category.assoc]; infer_instance
  have huc : UniversallyClosed (T'.subschemeι ≫ π) :=
    UniversallyClosed.of_comp_of_isSeparated _ f
  have hsupp : ((T'.map π).support : Set W) = Set.range (T'.subschemeι ≫ π) := by
    rw [Scheme.IdealSheafData.map, Scheme.Hom.support_ker]
    exact (T'.subschemeι ≫ π).isClosedMap.isClosed_range.closure_eq
  have hmul : T'.map π * T'' ≤ T'.map π ⊓ T'' := by
    intro U
    exact Ideal.mul_le_inf
  have hcov : ∀ x : (T'.map π ⊓ T'').subscheme, (∃ a, g₁ a = x) ∨ ∃ a, g₂ a = x := by
    intro x
    have hx : (T'.map π ⊓ T'').subschemeι x ∈ (T'.map π ⊓ T'').support := by
      rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
    have hx' := Scheme.IdealSheafData.support_antitone hmul hx
    rw [Scheme.IdealSheafData.support_mul] at hx'
    have hinj := (T'.map π ⊓ T'').subschemeι.isClosedEmbedding.injective
    rcases hx' with hx' | hx'
    · rw [hsupp] at hx'
      obtain ⟨a, ha⟩ := hx'
      refine Or.inl ⟨a, hinj ?_⟩
      rw [← ha, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.subschemeMap_subschemeι]
    · rw [← Scheme.IdealSheafData.range_subschemeι] at hx'
      obtain ⟨a, ha⟩ := hx'
      refine Or.inr ⟨a, hinj ?_⟩
      rw [← ha, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι]
  have huc' : UniversallyClosed ((T'.map π ⊓ T'').subschemeι ≫ f) :=
    universallyClosed_of_jointly_surjective g₁ g₂ _ hcov (e₁ ▸ inferInstance) (e₂ ▸ inferInstance)
  exact { }

end GlobalTheory
