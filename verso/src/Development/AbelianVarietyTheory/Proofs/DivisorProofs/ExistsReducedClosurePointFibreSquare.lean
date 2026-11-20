import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoIsMonHomOfIsGtOfRangeEq

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

/- English proof (translation)
Introduce `F _ Y K _ q₁ q₂ hq`. Set `ξ : Sp K ⟶ Limits.pullback Y.str Y.str` to `Limits.pullback.lift q₁ q₂ hq`. Set `x` to `ξ (IsLocalRing.closedPoint K)`. Set `i` to `GlobalTheory.MixHt.cloι x`. Establish `hw : (i ≫ Limits.pullback.fst Y.str Y.str) ≫ Y.str = (i ≫ Limits.pullback.snd Y.str Y.str) ≫ Y.str`.

Rewrite using `[Category.assoc, Category.assoc, Limits.pullback.condition]`. Establish `hl : Limits.pullback.lift _ _ hw = i`. Apply `Limits.pullback.hom_ext` to reduce the goal to its premises. Conclude with `Limits.pullback.lift_fst _ _ _`. Conclude with `Limits.pullback.lift_snd _ _ _`.

Establish `: IsReduced (Sp K)` using `inferInstanceAs (IsReduced (Spec _))`. Establish `hr : Set.range ξ ⊆ Set.range i`. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `ha : a = IsLocalRing.closedPoint K` using `Subsingleton.elim _ _`. Conclude with `⟨genericPoint _, by rw [ha, GlobalTheory.MixHt.cloι_genericPoint]⟩`.

Establish `hk : i.ker ≤ ξ.ker` using `ker_le_ker_of_range_subset_of_isReduced i ξ hr`. Set `ζ` to `IsClosedImmersion.lift i ξ hk`. Establish `hζ : ζ ≫ i = ξ` using `IsClosedImmersion.lift_fac _ _ _`. Use `⟨GlobalTheory.MixHt.clo x, inferInstance, i ≫ Limits.pullback.fst _ _, i ≫ Limits.pullback.snd _ _, hw, ζ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hl]`.

Use `infer_instance`. Rewrite using `[← Category.assoc, hζ]`. Conclude with `Limits.pullback.lift_fst _ _ _`. Rewrite using `[← Category.assoc, hζ]`. Conclude with `Limits.pullback.lift_snd _ _ _`.

Apply `i.isClosedEmbedding.injective` to reduce the goal to its premises. Use `(Scheme.Hom.comp_apply ζ i _).symm.trans ?_` and prove the remaining obligations. Rewrite using `[hζ, GlobalTheory.MixHt.cloι_genericPoint]`.
-/
theorem exists_closure_pair : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (q₁ q₂ : Sp K ⟶ Y.X), q₁ ≫ Y.str = q₂ ≫ Y.str → ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str) (ζ : Sp K ⟶ Z), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) ∧ ζ ≫ p₁ = q₁ ∧ ζ ≫ p₂ = q₂ ∧ ζ (IsLocalRing.closedPoint K) = genericPoint Z := by
  intro F _ Y K _ q₁ q₂ hq
  let ξ : Sp K ⟶ Limits.pullback Y.str Y.str := Limits.pullback.lift q₁ q₂ hq
  let x := ξ (IsLocalRing.closedPoint K)
  let i := GlobalTheory.MixHt.cloι x
  have hw : (i ≫ Limits.pullback.fst Y.str Y.str) ≫ Y.str = (i ≫ Limits.pullback.snd Y.str Y.str) ≫ Y.str := by
    rw [Category.assoc, Category.assoc, Limits.pullback.condition]
  have hl : Limits.pullback.lift _ _ hw = i := by
    apply Limits.pullback.hom_ext
    · exact Limits.pullback.lift_fst _ _ _
    · exact Limits.pullback.lift_snd _ _ _
  have : IsReduced (Sp K) := inferInstanceAs (IsReduced (Spec _))
  have hr : Set.range ξ ⊆ Set.range i := by
    rintro _ ⟨a, rfl⟩
    have ha : a = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact ⟨genericPoint _, by rw [ha, GlobalTheory.MixHt.cloι_genericPoint]⟩
  have hk : i.ker ≤ ξ.ker := ker_le_ker_of_range_subset_of_isReduced i ξ hr
  let ζ := IsClosedImmersion.lift i ξ hk
  have hζ : ζ ≫ i = ξ := IsClosedImmersion.lift_fac _ _ _
  refine ⟨GlobalTheory.MixHt.clo x, inferInstance, i ≫ Limits.pullback.fst _ _, i ≫ Limits.pullback.snd _ _, hw, ζ, ?_, ?_, ?_, ?_⟩
  · rw [hl]; infer_instance
  · rw [← Category.assoc, hζ]; exact Limits.pullback.lift_fst _ _ _
  · rw [← Category.assoc, hζ]; exact Limits.pullback.lift_snd _ _ _
  · apply i.isClosedEmbedding.injective
    refine (Scheme.Hom.comp_apply ζ i _).symm.trans ?_
    rw [hζ, GlobalTheory.MixHt.cloι_genericPoint]

end GlobalTheory.FlagPush
