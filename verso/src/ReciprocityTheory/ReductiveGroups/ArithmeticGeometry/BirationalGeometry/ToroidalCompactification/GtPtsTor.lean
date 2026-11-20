import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Semi.TorusPts

open TorusInj

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

/- English proof (translation)
Rewrite using `[charUnit_val, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]`. Use `congr 2`. Use `first`. Consider the case `(rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; simp only [Scheme.Hom.preimage_top])`. Consider the case `(simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top])`.

Consider the case `(ext1; simp [Scheme.Hom.appLE, Scheme.Hom.appTop])`.
-/
theorem charUnit_appTop {Z : Scheme.{0}} (τ : Z ⟶ (splitTorus S X).left) (χ : X) :
    τ.appTop.hom (charUnit S X χ).val =
      (τ ≫ tFst X).appTop.hom ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1)) := by
  rw [charUnit_val, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  congr 2
  first
  | (rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; simp only [Scheme.Hom.preimage_top])
  | (simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top])
  | (ext1; simp [Scheme.Hom.appLE, Scheme.Hom.appTop])

/- English proof (translation)
Use `AddMonoidAlgebra.ringHom_ext (fun b => ?_) h` and prove the remaining obligations. Establish `e : (AddMonoidAlgebra.single 0 b : AddMonoidAlgebra ZU.{0} X) = ((b.down : ℤ) : AddMonoidAlgebra ZU.{0} X)`. Rewrite using `[AddMonoidAlgebra.intCast_def]`. Use `congr 1`. Rewrite using `[e, map_intCast, map_intCast]`.
-/
theorem ringHom_ext_ZU {A : Type} [CommRing A] {f g : AddMonoidAlgebra ZU.{0} X →+* A}
    (h : ∀ χ, f (AddMonoidAlgebra.single χ 1) = g (AddMonoidAlgebra.single χ 1)) : f = g := by
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) h
  have e : (AddMonoidAlgebra.single 0 b : AddMonoidAlgebra ZU.{0} X) = ((b.down : ℤ) : AddMonoidAlgebra ZU.{0} X) := by
    rw [AddMonoidAlgebra.intCast_def]
    congr 1
  rw [e, map_intCast, map_intCast]

/- English proof (translation)
Establish `key : ∀ f g : Z.left ⟶ Spec (torusRing ZU X), (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ f.appTop = (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop → f = g`. Introduce `f g hfg`. Establish `hh : ∀ f' : Z.left ⟶ Spec (torusRing ZU X), (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ f'.appTop = ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop`. Introduce `f'`. Establish `h0` using `ΓSpecIso_inv_ΓSpec_adjunction_homEquiv ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop`.

Establish `hf : f' = ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X)) ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop.op` using `((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).apply_symm_apply f').symm`. Use `conv_lhs => rw [hf]`. Conclude with `h0`. Establish `hψ` using `(hh f).symm.trans (hfg.trans (hh g))`. Conclude with `(ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm.injective (congrArg Quiver.Hom.op hψ)`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Apply `key` to reduce the goal to its premises. Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Apply `ringHom_ext_ZU` to reduce the goal to its premises.

Introduce `χ`. Establish `e1` using `charUnit_appTop τ₁.left χ`. Establish `e2` using `charUnit_appTop τ₂.left χ`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply]`. Use `erw [← e1, ← e2]`.

Conclude with `h χ`. Conclude with `(Over.w τ₁).trans (Over.w τ₂).symm`.
-/
theorem torusPt_ext {Z : Over S} {τ₁ τ₂ : Z ⟶ splitTorus S X}
    (h : ∀ χ, τ₁.left.appTop.hom (charUnit S X χ).val = τ₂.left.appTop.hom (charUnit S X χ).val) :
    τ₁ = τ₂ := by
  have key : ∀ f g : Z.left ⟶ Spec (torusRing ZU X),
      (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ f.appTop = (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop →
        f = g := by
    intro f g hfg
    have hh : ∀ f' : Z.left ⟶ Spec (torusRing ZU X), (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ f'.appTop =
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop := by
      intro f'
      have h0 := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop
      have hf : f' = ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))
          ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop.op :=
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).apply_symm_apply f').symm
      conv_lhs => rw [hf]
      exact h0
    have hψ := (hh f).symm.trans (hfg.trans (hh g))
    exact (ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm.injective
      (congrArg Quiver.Hom.op hψ)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply key
    apply CommRingCat.hom_ext
    apply ringHom_ext_ZU
    intro χ
    have e1 := charUnit_appTop τ₁.left χ
    have e2 := charUnit_appTop τ₂.left χ
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    erw [← e1, ← e2]
    exact h χ
  · exact (Over.w τ₁).trans (Over.w τ₂).symm

end ReciprocityTheory.ChartRestriction.G.Semi.TorusPts
