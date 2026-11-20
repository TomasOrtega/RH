import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

/- English proof (translation)
Introduce `W W' Y Y₁ _ _ i _ h c _ s₁ U hiso hcomm hη hw`. Take `⟨w', hw'⟩` from `hw`. Use `⟨i ⁻¹ᵁ U, ⟨genericPoint W, hη⟩, ?_⟩` and prove the remaining obligations. Establish `hi : IsClosedImmersion (i ∣_ U)` using `IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) ‹_› U`. Establish `hc : IsClosedImmersion (c ∣_ (s₁ ⁻¹ᵁ U))` using `IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) ‹_› _`.

Establish `h1 : IsClosedImmersion ((c ≫ s₁) ∣_ U)`. Rewrite using `[morphismRestrict_comp]`. Establish `hs : IsClosedImmersion (s₁ ∣_ U)` using `inferInstance`. Conclude with `@IsClosedImmersion.comp _ _ _ _ _ hc hs`. Establish `h2 : IsClosedImmersion ((h ≫ i) ∣_ U)`.

Rewrite using `[hcomm]`. Conclude with `h1`. Rewrite `h2` using `[morphismRestrict_comp]`. Establish `h3 : IsClosedImmersion (h ∣_ (i ⁻¹ᵁ U))` using `@IsClosedImmersion.of_comp_isClosedImmersion _ _ _ _ (i ∣_ U) hi h2`. Establish `hw'U : w' ∈ h ⁻¹ᵁ (i ⁻¹ᵁ U)` using `by show h w' ∈ i ⁻¹ᵁ U`.

Rewrite using `[hw']`. Conclude with `hη`. Establish `h4 : Surjective (h ∣_ (i ⁻¹ᵁ U))`. Prove the components needed by the constructor for the conclusion. Introduce `x`.

Establish `hcl : IsClosed (Set.range (h ∣_ (i ⁻¹ᵁ U)))` using `(h ∣_ (i ⁻¹ᵁ U)).isClosedEmbedding.isClosed_range`. Set `p : (h ⁻¹ᵁ (i ⁻¹ᵁ U) : Scheme)` to `⟨w', hw'U⟩`. Establish `hp : ((h ∣_ (i ⁻¹ᵁ U)) p).1 = genericPoint W`. Rewrite using `[morphismRestrict_base_coe]`. Conclude with `hw'`.

Establish `hsp : (h ∣_ (i ⁻¹ᵁ U)) p ⤳ x`. Rewrite using `[← (i ⁻¹ᵁ U).ι.isOpenEmbedding.toIsInducing.specializes_iff]`. Establish `: (i ⁻¹ᵁ U).ι ((h ∣_ (i ⁻¹ᵁ U)) p) = genericPoint W` using `hp`. Rewrite using `[this]`. Conclude with `(genericPoint_spec W).specializes (Set.mem_univ _)`.

Conclude with `hsp.mem_closed hcl ⟨p, rfl⟩`. Conclude with `isIso_of_isClosedImmersion_of_surjective _`.
-/
theorem isIso_restrict_of_closedImmersion_near_generic :
    ∀ {W W' Y Y₁ : Scheme.{0}} [IsIntegral W] [IsIntegral W'] (i : W ⟶ Y) [IsClosedImmersion i] (h : W' ⟶ W)
      (c : W' ⟶ Y₁) [IsClosedImmersion c] (s₁ : Y₁ ⟶ Y) (U : Y.Opens), IsIso (s₁ ∣_ U) → h ≫ i = c ≫ s₁ →
      i (genericPoint W) ∈ U → (∃ w', h w' = genericPoint W) →
      ∃ U' : W.Opens, (U' : Set W).Nonempty ∧ IsIso (h ∣_ U') := by
  intro W W' Y Y₁ _ _ i _ h c _ s₁ U hiso hcomm hη hw
  obtain ⟨w', hw'⟩ := hw
  refine ⟨i ⁻¹ᵁ U, ⟨genericPoint W, hη⟩, ?_⟩
  have hi : IsClosedImmersion (i ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) ‹_› U
  have hc : IsClosedImmersion (c ∣_ (s₁ ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) ‹_› _
  have h1 : IsClosedImmersion ((c ≫ s₁) ∣_ U) := by
    rw [morphismRestrict_comp]
    have hs : IsClosedImmersion (s₁ ∣_ U) := inferInstance
    exact @IsClosedImmersion.comp _ _ _ _ _ hc hs
  have h2 : IsClosedImmersion ((h ≫ i) ∣_ U) := by
    rw [hcomm]; exact h1
  rw [morphismRestrict_comp] at h2
  have h3 : IsClosedImmersion (h ∣_ (i ⁻¹ᵁ U)) :=
    @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ _ (i ∣_ U) hi h2
  have hw'U : w' ∈ h ⁻¹ᵁ (i ⁻¹ᵁ U) := by
    show h w' ∈ i ⁻¹ᵁ U
    rw [hw']; exact hη
  have h4 : Surjective (h ∣_ (i ⁻¹ᵁ U)) := by
    constructor
    intro x
    have hcl : IsClosed (Set.range (h ∣_ (i ⁻¹ᵁ U))) := (h ∣_ (i ⁻¹ᵁ U)).isClosedEmbedding.isClosed_range
    let p : (h ⁻¹ᵁ (i ⁻¹ᵁ U) : Scheme) := ⟨w', hw'U⟩
    have hp : ((h ∣_ (i ⁻¹ᵁ U)) p).1 = genericPoint W := by
      rw [morphismRestrict_base_coe]; exact hw'
    have hsp : (h ∣_ (i ⁻¹ᵁ U)) p ⤳ x := by
      rw [← (i ⁻¹ᵁ U).ι.isOpenEmbedding.toIsInducing.specializes_iff]
      have : (i ⁻¹ᵁ U).ι ((h ∣_ (i ⁻¹ᵁ U)) p) = genericPoint W := hp
      rw [this]
      exact (genericPoint_spec W).specializes (Set.mem_univ _)
    exact hsp.mem_closed hcl ⟨p, rfl⟩
  exact isIso_of_isClosedImmersion_of_surjective _

end GlobalTheory
