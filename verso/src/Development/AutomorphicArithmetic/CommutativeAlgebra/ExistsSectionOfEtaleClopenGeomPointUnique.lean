import Development.AutomorphicArithmetic.SpecialMaps.QuotObjDefs
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

/- English proof (translation)
Introduce `S Y hfin het W hWo hWc hex huniq`. Set `U : Y.left.Opens` to `⟨W, hWo⟩`. Establish `hrange : Set.range U.ι.base = W` using `U.range_ι`. Use `haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by rw [hrange]; exact hWc)`. Use `haveI : IsFinite (U.ι ≫ Y.hom) := inferInstance`.

Use `haveI : Etale (U.ι ≫ Y.hom) := inferInstance`. Establish `hiso : IsIso (U.ι ≫ Y.hom)`. Rewrite using `[GlobalTheory.FinEt.isIso_iff_bijective_algClosed]`. Introduce `k _ _`. Prove the components needed by the constructor for the conclusion.

Introduce `z₁ z₂ h`. Apply `(cancel_mono U.ι).mp` to reduce the goal to its premises. Apply `huniq k (z₁ ≫ U.ι) (z₂ ≫ U.ι)` to reduce the goal to its premises. Simplify `h` using `[Category.assoc]`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange.symm]`.

Conclude with `Set.image_subset_range _ _`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange.symm]`. Conclude with `Set.image_subset_range _ _`. Introduce `x`. Take `⟨y, hy, hyW⟩` from `hex k x`.

Use `⟨IsOpenImmersion.lift U.ι y (by rw [hrange]; exact hyW), ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← Category.assoc, IsOpenImmersion.lift_fac, hy]`. Use `⟨inv (U.ι ≫ Y.hom) ≫ U.ι, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, IsIso.inv_hom_id]`.

Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← hrange]`. Conclude with `Set.image_subset_range _ _`.
-/
theorem UpperTheory.exists_section_of_etale_clopen_geomPoint_unique :
    ∀ (S : Scheme.{0}) (Y : Over S), IsFinite Y.hom → Etale Y.hom → ∀ (W : Set Y.left), IsOpen W → IsClosed W → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ y : Sp k ⟶ Y.left, y ≫ Y.hom = x ∧ Set.range y.base ⊆ W) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y₁ y₂ : Sp k ⟶ Y.left), y₁ ≫ Y.hom = y₂ ≫ Y.hom → Set.range y₁.base ⊆ W → Set.range y₂.base ⊆ W → y₁ = y₂) → ∃ σ : S ⟶ Y.left, σ ≫ Y.hom = 𝟙 S ∧ Set.range σ.base ⊆ W := by
  intro S Y hfin het W hWo hWc hex huniq
  let U : Y.left.Opens := ⟨W, hWo⟩
  have hrange : Set.range U.ι.base = W := U.range_ι
  haveI : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [hrange]; exact hWc)
  haveI : IsFinite (U.ι ≫ Y.hom) := inferInstance
  haveI : Etale (U.ι ≫ Y.hom) := inferInstance
  have hiso : IsIso (U.ι ≫ Y.hom) := by
    rw [GlobalTheory.FinEt.isIso_iff_bijective_algClosed]
    intro k _ _
    constructor
    · intro z₁ z₂ h
      apply (cancel_mono U.ι).mp
      apply huniq k (z₁ ≫ U.ι) (z₂ ≫ U.ι)
      · simpa [Category.assoc] using h
      · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange.symm]
        exact Set.image_subset_range _ _
      · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange.symm]
        exact Set.image_subset_range _ _
    · intro x
      obtain ⟨y, hy, hyW⟩ := hex k x
      refine ⟨IsOpenImmersion.lift U.ι y (by rw [hrange]; exact hyW), ?_⟩
      simp only
      rw [← Category.assoc, IsOpenImmersion.lift_fac, hy]
  refine ⟨inv (U.ι ≫ Y.hom) ≫ U.ι, ?_, ?_⟩
  · rw [Category.assoc, IsIso.inv_hom_id]
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← hrange]
    exact Set.image_subset_range _ _
