import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

noncomputable section

namespace GlobalTheory.Mum.Conj

variable {R : Type} [CommRing R] [IsDomain R]

/- English proof (translation)
Use `ext1`. Rewrite using `[Over.comp_left, twK_left, twK_left, Over.id_left, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Establish `: τ.toRingHom.comp σ.toRingHom = RingHom.id _` using `congrArg AlgHom.toRingHom h`. Rewrite using `[this]`. Conclude with `Spec.map_id _`.
-/
theorem twK_comp_twK (σ τ : Kb R →ₐ[FractionRing R] Kb R) (h : τ.comp σ = AlgHom.id _ _) :
    twK τ ≫ twK σ = 𝟙 _ := by
  ext1
  rw [Over.comp_left, twK_left, twK_left, Over.id_left, spMap, spMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have : τ.toRingHom.comp σ.toRingHom = RingHom.id _ := congrArg AlgHom.toRingHom h
  rw [this]
  exact Spec.map_id _

/- English proof (translation)
Rewrite using `[← Over.comp_left]`. Establish `: mTw A τ ≫ mTw A σ = 𝟙 _`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, mTw_fst, ← Category.assoc, mTw_fst, Category.assoc, twK_comp_twK σ τ h, Category.comp_id, Category.id_comp]`. Rewrite using `[Category.assoc, mTw_snd, mTw_snd, Category.id_comp]`.

Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem mTw_comp_mTw_left (A : PolAV (Sp (FractionRing R))) (σ τ : Kb R →ₐ[FractionRing R] Kb R)
    (h : τ.comp σ = AlgHom.id _ _) : (mTw A τ).left ≫ (mTw A σ).left = 𝟙 _ := by
  rw [← Over.comp_left]
  have : mTw A τ ≫ mTw A σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, mTw_fst, ← Category.assoc, mTw_fst, Category.assoc, twK_comp_twK σ τ h,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, mTw_snd, mTw_snd, Category.id_comp]
  rw [this]; rfl

/- English proof (translation)
Use `GlobalTheory.FieldBaseChange.sec_ext' A.isLB fun y J hJ => ?_` and prove the remaining obligations. Use `(GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans ((GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc, mTw_comp_mTw_left A σ τ h, Category.comp_id]`.
-/
theorem secTw_secTw (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ τ : Kb R →ₐ[FractionRing R] Kb R)
    (h : τ.comp σ = AlgHom.id _ _) (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) :
    secTw A N τ (secTw A N σ t) = t := by
  refine GlobalTheory.FieldBaseChange.sec_ext' A.isLB fun y J hJ => ?_
  refine (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans
    ((GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans ?_)
  rw [Category.assoc, mTw_comp_mTw_left A σ τ h, Category.comp_id]

/- English proof (translation)
Establish `hσ : Function.Bijective σ` using `Algebra.IsAlgebraic.algHom_bijective σ`. Set `e` to `AlgEquiv.ofBijective σ hσ`. Set `τ : Kb R →ₐ[FractionRing R] Kb R` to `e.symm.toAlgHom`. Establish `h1 : τ.comp σ = AlgHom.id _ _`. Use extensionality with `x`.

Conclude with `e.symm_apply_apply x`. Establish `h2 : σ.comp τ = AlgHom.id _ _`. Use extensionality with `x`. Conclude with `e.apply_symm_apply x`. Conclude with `⟨Function.LeftInverse.injective (g := secTw A N τ) (secTw_secTw A N σ τ h1), Function.RightInverse.surjective (g := secTw A N τ) (secTw_secTw A N τ σ h2)⟩`.
-/
theorem secTw_bijective (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) : Function.Bijective (secTw A N σ) := by
  have hσ : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  let e := AlgEquiv.ofBijective σ hσ
  let τ : Kb R →ₐ[FractionRing R] Kb R := e.symm.toAlgHom
  have h1 : τ.comp σ = AlgHom.id _ _ := by
    ext x; exact e.symm_apply_apply x
  have h2 : σ.comp τ = AlgHom.id _ _ := by
    ext x; exact e.apply_symm_apply x
  exact ⟨Function.LeftInverse.injective (g := secTw A N τ) (secTw_secTw A N σ τ h1),
    Function.RightInverse.surjective (g := secTw A N τ) (secTw_secTw A N τ σ h2)⟩

end GlobalTheory.Mum.Conj
