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
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
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
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem secTw_secTw (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ τ : Kb R →ₐ[FractionRing R] Kb R)
    (h : τ.comp σ = AlgHom.id _ _) (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) :
    secTw A N τ (secTw A N σ t) = t := by
  refine GlobalTheory.FieldBaseChange.sec_ext' A.isLB fun y J hJ => ?_
  refine (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans
    ((GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans ?_)
  rw [Category.assoc, mTw_comp_mTw_left A σ τ h, Category.comp_id]

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components.

Establish an intermediate fact. By extensionality, compare the relevant components. Supply the required witnesses or components. A detailed English derivation is pending.
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
