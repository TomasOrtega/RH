import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ Y hY W hW`. Set `alg : R →+* Γ(Y.left, W)` to `(Y.hom.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom`. Use `letI : Algebra R Γ(Y.left, W) := alg.toAlgebra`. Establish `s₀ : hW.fromSpec ≫ Y.hom = spMap alg`. Rewrite using `[← IsAffineOpen.SpecMap_appLE_fromSpec Y.hom (isAffineOpen_top _) hW (fun _ _ => trivial), IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]`.

Both sides reduce to the same expression. Establish `h1 : RingHom.Smooth (Y.hom.appLE ⊤ W (fun _ _ => trivial)).hom` using `HasRingHomProperty.appLE @Smooth Y.hom hY ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)`. Establish `h2 : RingHom.Smooth alg` using `RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1`. Conclude with `⟨Γ(Y.left, W), inferInstance, inferInstance, hW.fromSpec, inferInstance, hW.opensRange_fromSpec, s₀, h2⟩`.
-/
theorem affineChart_smooth : ∀ (R : Type) [CommRing R] (Y : Over (Sp R)), Smooth Y.hom → ∀ (W : Y.left.Opens), IsAffineOpen W → ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O) (k : Sp O ⟶ Y.left) (_ : IsOpenImmersion k), k.opensRange = W ∧ k ≫ Y.hom = spMap (algebraMap R O) ∧ Algebra.Smooth R O := by
  intro R _ Y hY W hW
  let alg : R →+* Γ(Y.left, W) :=
    (Y.hom.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  letI : Algebra R Γ(Y.left, W) := alg.toAlgebra
  have s₀ : hW.fromSpec ≫ Y.hom = spMap alg := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec Y.hom (isAffineOpen_top _) hW (fun _ _ => trivial),
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]; rfl
  have h1 : RingHom.Smooth (Y.hom.appLE ⊤ W (fun _ _ => trivial)).hom :=
    HasRingHomProperty.appLE @Smooth Y.hom hY ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)
  have h2 : RingHom.Smooth alg :=
    RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
  exact ⟨Γ(Y.left, W), inferInstance, inferInstance, hW.fromSpec, inferInstance, hW.opensRange_fromSpec, s₀, h2⟩

end GlobalTheory.Mum
