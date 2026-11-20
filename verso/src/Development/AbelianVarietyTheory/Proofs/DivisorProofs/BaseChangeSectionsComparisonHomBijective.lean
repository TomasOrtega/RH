import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfIsPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BaseChg

/- English proof (translation)
Introduce `R₀ R₁ _ _ _ X₀ X₁ s₀ s₁ pr hp U`. Establish `po` using `(isIso_pushoutSection_iff hp (US := ⊤) (UT := ⊤) (UX := U.1) (UY := pr ⁻¹ᵁ U.1) le_top le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hp _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) U.2)`. Establish `po' : IsPushout (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom (algebraMap R₀ (Sec s₀ U.1))) (CommRingCat.ofHom (algebraMap R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)))) (pr.appLE U.1 (pr ⁻¹ᵁ U.1) le_rfl)`. Use `po.flip.of_iso (Scheme.ΓSpecIso (CommRingCat.of R₀)) (Scheme.ΓSpecIso (CommRingCat.of R₁)) (Iso.refl (CommRingCat.of (Sec s₀ U.1))) (Iso.refl (CommRingCat.of (Sec s₁ (pr ⁻¹ᵁ U.1)))) ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`.

Both sides reduce to the same expression. Use extensionality with `r`. Express the relevant statement in the definitionally equal form `(s₀.appLE ⊤ U.1 le_top).hom r = (s₀.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).hom.hom r))`. Use `congr 1`. Simplify using the standard rewrite rules.

Use extensionality with `r`. Express the relevant statement in the definitionally equal form `(s₁.appLE ⊤ (pr ⁻¹ᵁ U.1) _).hom r = (s₁.appLE ⊤ (pr ⁻¹ᵁ U.1) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).hom.hom r))`. Use `congr 1`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Establish `h1` using `CommRingCat.isPushout_tensorProduct R₀ R₁ (Sec s₀ U.1)`. Set `e` to `h1.isoIsPushout _ _ po'`. Establish `he : e.hom = CommRingCat.ofHom (beta hp U)`. Use `h1.hom_ext ?_ ?_` and prove the remaining obligations. Use `(h1.inl_isoIsPushout_hom _ _ po').trans ?_` and prove the remaining obligations.

Use extensionality with `r`. Express the relevant statement in the definitionally equal form `algebraMap R₁ _ r = beta hp U (r ⊗ₜ 1)`. Rewrite using `[beta_tmul, map_one, _root_.mul_one]`. Use `(h1.inr_isoIsPushout_hom _ _ po').trans ?_` and prove the remaining obligations. Use extensionality with `b`.

Express the relevant statement in the definitionally equal form `(pr.appLE U.1 (pr ⁻¹ᵁ U.1) le_rfl).hom b = beta hp U (1 ⊗ₜ b)`. Use `Eq.trans ?_ (beta_tmul hp U 1 b).symm` and prove the remaining obligations. Rewrite using `[map_one, _root_.one_mul]`. Both sides reduce to the same expression. Establish `hb` using `ConcreteCategory.bijective_of_isIso e.hom`.

Rewrite `hb` using `[he]`. Conclude with `hb`.
-/
theorem beta_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀)
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens),
    Function.Bijective (GlobalTheory.Obs.BaseChg.beta hp U) := by
  intro R₀ R₁ _ _ _ X₀ X₁ s₀ s₁ pr hp U
  have po := (isIso_pushoutSection_iff hp (US := ⊤) (UT := ⊤) (UX := U.1) (UY := pr ⁻¹ᵁ U.1) le_top le_top
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hp _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) U.2)
  have po' : IsPushout (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom (algebraMap R₀ (Sec s₀ U.1)))
      (CommRingCat.ofHom (algebraMap R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)))) (pr.appLE U.1 (pr ⁻¹ᵁ U.1) le_rfl) := by
    refine po.flip.of_iso (Scheme.ΓSpecIso (CommRingCat.of R₀)) (Scheme.ΓSpecIso (CommRingCat.of R₁))
      (Iso.refl (CommRingCat.of (Sec s₀ U.1))) (Iso.refl (CommRingCat.of (Sec s₁ (pr ⁻¹ᵁ U.1)))) ?_ ?_ ?_ ?_
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · ext r
      change (s₀.appLE ⊤ U.1 le_top).hom r = (s₀.appLE ⊤ U.1 le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).hom.hom r))
      congr 1
      simp
    · ext r
      change (s₁.appLE ⊤ (pr ⁻¹ᵁ U.1) _).hom r = (s₁.appLE ⊤ (pr ⁻¹ᵁ U.1) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).hom.hom r))
      congr 1
      simp
    · rfl
  have h1 := CommRingCat.isPushout_tensorProduct R₀ R₁ (Sec s₀ U.1)
  let e := h1.isoIsPushout _ _ po'
  have he : e.hom = CommRingCat.ofHom (beta hp U) := by
    refine h1.hom_ext ?_ ?_
    · refine (h1.inl_isoIsPushout_hom _ _ po').trans ?_
      ext r
      change algebraMap R₁ _ r = beta hp U (r ⊗ₜ 1)
      rw [beta_tmul, map_one, _root_.mul_one]
    · refine (h1.inr_isoIsPushout_hom _ _ po').trans ?_
      ext b
      change (pr.appLE U.1 (pr ⁻¹ᵁ U.1) le_rfl).hom b = beta hp U (1 ⊗ₜ b)
      refine Eq.trans ?_ (beta_tmul hp U 1 b).symm
      rw [map_one, _root_.one_mul]
      rfl
  have hb := ConcreteCategory.bijective_of_isIso e.hom
  rw [he] at hb
  exact hb

end GlobalTheory.Obs.BaseChg
