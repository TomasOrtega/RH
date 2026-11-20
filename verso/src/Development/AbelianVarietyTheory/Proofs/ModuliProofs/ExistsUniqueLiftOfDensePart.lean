import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

/- English proof (translation)
Use `isIso_stalkMap_of_flat_of_surjectiveOnStalks j` as an intermediate fact. Establish `: GlobalTheory.IsNormalScheme U` using `GlobalTheory.IsNormalScheme.of_isIso_stalkMap j`. Establish `hη : genericPoint T ∈ genericPoints T`. Rewrite using `[genericPoints_eq_singleton]`. Both sides reduce to the same expression.

Take `⟨u, hu⟩` from `genericPoints_subset_range_of_isDominant j hη`. Establish `hgen : IsGenericPoint u (Set.univ : Set U)`. Rewrite using `[isGenericPoint_iff_specializes]`. Use `fun y => ⟨fun _ => trivial, fun _ => ?_⟩` and prove the remaining obligations. Rewrite using `[← j.isEmbedding.isInducing.specializes_iff, hu]`.

Conclude with `(genericPoint_spec T).specializes trivial`. Establish `: IrreducibleSpace U`. Rewrite using `[irreducibleSpace_def]`. Conclude with `hgen.isIrreducible`. Conclude with `GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace U`.
-/
theorem isIntegral_of_densePart {T U : Scheme.{0}} (j : U ⟶ T) [IsIntegral T]
    [GlobalTheory.IsNormalScheme T] [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] :
    IsIntegral U := by
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j
  have : GlobalTheory.IsNormalScheme U := GlobalTheory.IsNormalScheme.of_isIso_stalkMap j
  have hη : genericPoint T ∈ genericPoints T := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨u, hu⟩ := genericPoints_subset_range_of_isDominant j hη
  have hgen : IsGenericPoint u (Set.univ : Set U) := by
    rw [isGenericPoint_iff_specializes]
    refine fun y => ⟨fun _ => trivial, fun _ => ?_⟩
    rw [← j.isEmbedding.isInducing.specializes_iff, hu]
    exact (genericPoint_spec T).specializes trivial
  have : IrreducibleSpace U := by
    rw [irreducibleSpace_def]
    exact hgen.isIrreducible
  exact GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace U

/- English proof (translation)
Introduce `T U Y Z _ j hT _ _ _ _ p b a _ h`. Use `GlobalTheory.IsNormalScheme.of_pred hT` as an intermediate fact. Establish `H (W : irreducibleComponents T)`. Establish `: IsDominant (j ∣_ GlobalTheory.IsNormalScheme.component W)` using `IsZariskiLocalAtTarget.restrict (P := @IsDominant) ‹IsDominant j› _`. Establish `: IsIntegral (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).toScheme` using `isIntegral_of_densePart (j ∣_ GlobalTheory.IsNormalScheme.component W)`.

Use `isIso_stalkMap_of_flat_of_surjectiveOnStalks (j ∣_ GlobalTheory.IsNormalScheme.component W)` as an intermediate fact. Conclude with `existsUnique_lift_of_birational (j ∣_ GlobalTheory.IsNormalScheme.component W) p ((j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ a) ((GlobalTheory.IsNormalScheme.component W).ι ≫ b) (by rw [Category.assoc, h, morphismRestrict_ι_assoc])`. Use `choose c hc _ using H`. Take `⟨hT⟩` from `GlobalTheory.IsNormalScheme.nonempty_isColimit_component T`. Set `c₀ : T ⟶ Z` to `Cofan.IsColimit.desc hT c`.

Establish `hc₀ (W) : (GlobalTheory.IsNormalScheme.component W).ι ≫ c₀ = c W` using `Cofan.IsColimit.fac hT c W`. Establish `h₂ : c₀ ≫ p = b` using `Cofan.IsColimit.hom_ext hT _ _ fun W ↦ by`. Express the relevant statement in the definitionally equal form `(GlobalTheory.IsNormalScheme.component W).ι ≫ _ = (GlobalTheory.IsNormalScheme.component W).ι ≫ _`. Rewrite using `[reassoc_of% hc₀ W, (hc W).2]`. Establish `h₁ : j ≫ c₀ = a`.

Use `Scheme.Cover.hom_ext (U.openCoverOfIsOpenCover _ (.comap (GlobalTheory.IsNormalScheme.iSup_component T) j.base.1)) _ _ fun W ↦ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ _ = (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ _`. Rewrite using `[← morphismRestrict_ι_assoc, hc₀ W, (hc W).1]`. Conclude with `⟨c₀, ⟨h₁, h₂⟩, fun c' hc' ↦ lift_unique_of_isDominant j p (hc'.1.trans h₁.symm) (hc'.2.trans h₂.symm)⟩`.
-/
theorem existsUnique_lift_of_densePart : ∀ (T U X Y : Scheme.{0}) [IsLocallyNoetherian T] (j : U ⟶ T), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (q : Y ⟶ X) (f : T ⟶ X) (g : U ⟶ Y), IsIntegralHom q → g ≫ q = j ≫ f → ∃! h : T ⟶ Y, j ≫ h = g ∧ h ≫ q = f := by
  intro T U Y Z _ j hT _ _ _ _ p b a _ h
  have := GlobalTheory.IsNormalScheme.of_pred hT
  have H (W : irreducibleComponents T) := by
    have : IsDominant (j ∣_ GlobalTheory.IsNormalScheme.component W) :=
      IsZariskiLocalAtTarget.restrict (P := @IsDominant) ‹IsDominant j› _
    have : IsIntegral (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).toScheme :=
      isIntegral_of_densePart (j ∣_ GlobalTheory.IsNormalScheme.component W)
    have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (j ∣_ GlobalTheory.IsNormalScheme.component W)
    exact existsUnique_lift_of_birational (j ∣_ GlobalTheory.IsNormalScheme.component W) p
      ((j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ a) ((GlobalTheory.IsNormalScheme.component W).ι ≫ b)
      (by rw [Category.assoc, h, morphismRestrict_ι_assoc])
  choose c hc _ using H
  obtain ⟨hT⟩ := GlobalTheory.IsNormalScheme.nonempty_isColimit_component T
  let c₀ : T ⟶ Z := Cofan.IsColimit.desc hT c
  have hc₀ (W) : (GlobalTheory.IsNormalScheme.component W).ι ≫ c₀ = c W := Cofan.IsColimit.fac hT c W
  have h₂ : c₀ ≫ p = b := Cofan.IsColimit.hom_ext hT _ _ fun W ↦ by
    change (GlobalTheory.IsNormalScheme.component W).ι ≫ _ = (GlobalTheory.IsNormalScheme.component W).ι ≫ _
    rw [reassoc_of% hc₀ W, (hc W).2]
  have h₁ : j ≫ c₀ = a := by
    refine Scheme.Cover.hom_ext (U.openCoverOfIsOpenCover _
      (.comap (GlobalTheory.IsNormalScheme.iSup_component T) j.base.1)) _ _ fun W ↦ ?_
    change (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ _ =
      (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ _
    rw [← morphismRestrict_ι_assoc, hc₀ W, (hc W).1]
  exact ⟨c₀, ⟨h₁, h₂⟩, fun c' hc' ↦
    lift_unique_of_isDominant j p (hc'.1.trans h₁.symm) (hc'.2.trans h₂.symm)⟩

end GlobalTheory
