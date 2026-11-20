import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AffInj

/- English proof (translation)
Use `algebraize [φ.hom, ψ.hom]`. Set `e` to `(CommRingCat.isPushout_tensorProduct R A K).isoIsPushout _ _ H`. Establish `h1 : inr = _ ≫ e.hom` using `(IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R A K) H).symm`. Rewrite using `[h1, CommRingCat.hom_comp, RingHom.coe_comp]`. Use `(ConcreteCategory.injective_of_mono_of_preservesPullback e.hom).comp ?_` and prove the remaining obligations.

Establish `hinj` using `Module.Flat.rTensor_preserves_injective_linearMap (M := K) (Algebra.linearMap R A) hφ`. Introduce `a b hab`. Apply `(TensorProduct.lid R K).symm.injective` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Simplify using `using hab`.
-/
theorem inr_injective_of_isPushout {R A K P : CommRingCat.{0}} {φ : R ⟶ A} {ψ : R ⟶ K}
    {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout φ ψ inl inr) (hφ : Function.Injective φ.hom)
    (hψ : ψ.hom.Flat) : Function.Injective inr.hom := by
  algebraize [φ.hom, ψ.hom]
  let e := (CommRingCat.isPushout_tensorProduct R A K).isoIsPushout _ _ H
  have h1 : inr = _ ≫ e.hom :=
    (IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R A K) H).symm
  rw [h1, CommRingCat.hom_comp, RingHom.coe_comp]
  refine (ConcreteCategory.injective_of_mono_of_preservesPullback e.hom).comp ?_
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := K)
    (Algebra.linearMap R A) hφ
  intro a b hab
  apply (TensorProduct.lid R K).symm.injective
  apply hinj
  simpa using hab

end GlobalTheory.AffInj

namespace GlobalTheory.AffInj

/- English proof (translation)
Establish `: CompactSpace S` using `QuasiCompact.compactSpace_of_compactSpace π`. Establish `hUY : p ⁻¹ᵁ V = q ⁻¹ᵁ ⊤ ⊓ p ⁻¹ᵁ V` using `by simp`. Establish `hST : V ≤ y ⁻¹ᵁ ⊤` using `le_top`. Establish `hSX : (⊤ : S.Opens) ≤ π ⁻¹ᵁ ⊤` using `le_top`. Set `σ` to `pushoutSection H.flip hST hSX hUY`.

Establish `hm : Mono σ` using `mono_pushoutSection_of_isCompact_of_flat_right H.flip hST hSX hUY (isAffineOpen_top _) hV (by simpa using isCompact_univ)`. Establish `hσ : Function.Injective σ.hom` using `(ConcreteCategory.mono_iff_injective_of_preservesPullback σ).mp hm`. Establish `h1 : pushout.inr _ _ ≫ σ = p.appLE V (p ⁻¹ᵁ V) le_rfl` using `pushout.inr_desc _ _ _`. Establish `hφ : Function.Injective (π.appLE ⊤ ⊤ hSX).hom`. Establish `e : π.appLE ⊤ ⊤ hSX = π.appTop` using `(Scheme.Hom.app_eq_appLE π (U := ⊤)).symm`.

Rewrite using `[e]`. Conclude with `hinj`. Establish `hinr` using `inr_injective_of_isPushout (IsPushout.of_hasPushout (π.appLE ⊤ ⊤ hSX) (y.appLE ⊤ V hST)) hφ (y.flat_appLE (isAffineOpen_top _) hV _)`. Establish `h2 : p.app V = p.appLE V (p ⁻¹ᵁ V) le_rfl` using `Scheme.Hom.app_eq_appLE p`. Rewrite using `[h2, ← h1, CommRingCat.hom_comp, RingHom.coe_comp]`.

Conclude with `hσ.comp hinr`.
-/
theorem app_injective_of_isPullback (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R)
    (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S) (hπ : IsProper π) (hy : Flat y)
    (H : IsPullback p q y π) (hinj : Function.Injective π.appTop.hom) (V : Y.Opens)
    (hV : IsAffineOpen V) : Function.Injective (p.app V).hom := by
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  have hUY : p ⁻¹ᵁ V = q ⁻¹ᵁ ⊤ ⊓ p ⁻¹ᵁ V := by simp
  have hST : V ≤ y ⁻¹ᵁ ⊤ := le_top
  have hSX : (⊤ : S.Opens) ≤ π ⁻¹ᵁ ⊤ := le_top
  let σ := pushoutSection H.flip hST hSX hUY
  have hm : Mono σ := mono_pushoutSection_of_isCompact_of_flat_right H.flip hST hSX hUY
    (isAffineOpen_top _) hV (by simpa using isCompact_univ)
  have hσ : Function.Injective σ.hom := (ConcreteCategory.mono_iff_injective_of_preservesPullback σ).mp hm
  have h1 : pushout.inr _ _ ≫ σ = p.appLE V (p ⁻¹ᵁ V) le_rfl := pushout.inr_desc _ _ _
  have hφ : Function.Injective (π.appLE ⊤ ⊤ hSX).hom := by
    have e : π.appLE ⊤ ⊤ hSX = π.appTop := (Scheme.Hom.app_eq_appLE π (U := ⊤)).symm
    rw [e]; exact hinj
  have hinr := inr_injective_of_isPushout (IsPushout.of_hasPushout (π.appLE ⊤ ⊤ hSX)
    (y.appLE ⊤ V hST)) hφ (y.flat_appLE (isAffineOpen_top _) hV _)
  have h2 : p.app V = p.appLE V (p ⁻¹ᵁ V) le_rfl := Scheme.Hom.app_eq_appLE p
  rw [h2, ← h1, CommRingCat.hom_comp, RingHom.coe_comp]
  exact hσ.comp hinr

/- English proof (translation)
The claim follows from `@app_injective_of_isPullback`.
-/
example : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → Function.Injective π.appTop.hom → ∀ V : Y.Opens, IsAffineOpen V → Function.Injective (p.app V).hom :=
  @app_injective_of_isPullback

end GlobalTheory.AffInj
