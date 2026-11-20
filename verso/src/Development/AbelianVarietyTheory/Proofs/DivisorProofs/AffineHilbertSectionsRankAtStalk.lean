import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.HilbAff

/- English proof (translation)
The claim follows from `(IsOpenImmersion.isPullback _ _ _ _ (by rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec π hW hV]) (by simp)).flip`.
-/
theorem isPullback_fromSpec_app_rank {X Y : Scheme.{0}} (π : X ⟶ Y) {W : Y.Opens}
    (hW : IsAffineOpen W) (hV : IsAffineOpen (π ⁻¹ᵁ W)) :
    IsPullback hV.fromSpec (Spec.map (π.app W)) π hW.fromSpec :=
  (IsOpenImmersion.isPullback _ _ _ _ (by
    rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec π hW hV]) (by simp)).flip

/- English proof (translation)
Take `⟨_hfin, _hflat, h3⟩` from `y.2.2`. Establish `hW : IsAffineOpen (W : Z.Opens)` using `W.2`. Establish `hV : IsAffineOpen (subStr A B y ⁻¹ᵁ (W : Z.Opens))` using `hW.preimage _`. Use `haveI : Module.Finite Γ(Z, W) (Sec A B y W) := by`. Use `IsFinite.finite_app (subStr A B y) (W : Z.Opens) hW` as an intermediate fact.

Conclude with `this`. Use `haveI : Module.Flat Γ(Z, W) (Sec A B y W) := by`. Use `Scheme.Hom.flat_appLE (subStr A B y) hW hV le_rfl` as an intermediate fact. Rewrite `this` using `[Scheme.Hom.appLE_eq_app]`. Conclude with `this`.

Establish `e` using `Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_fromSpec_app_rank (subStr A B y) hW hV) P`. Rewrite `e` using `[h3]`. Rewrite using `[← Scheme.Hom.finrank_SpecMap_algebraMap]`. Conclude with `e`.
-/
theorem rankAtStalk_sec (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    (Z : Scheme.{0}) (y : (functor A B r).obj (op Z)) (W : Z.affineOpens)
    (P : PrimeSpectrum Γ(Z, W)) : Module.rankAtStalk (Sec A B y W) P = r := by
  obtain ⟨_hfin, _hflat, h3⟩ := y.2.2
  have hW : IsAffineOpen (W : Z.Opens) := W.2
  have hV : IsAffineOpen (subStr A B y ⁻¹ᵁ (W : Z.Opens)) := hW.preimage _
  haveI : Module.Finite Γ(Z, W) (Sec A B y W) := by
    have := IsFinite.finite_app (subStr A B y) (W : Z.Opens) hW
    exact this
  haveI : Module.Flat Γ(Z, W) (Sec A B y W) := by
    have := Scheme.Hom.flat_appLE (subStr A B y) hW hV le_rfl
    rw [Scheme.Hom.appLE_eq_app] at this
    exact this
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _
    (isPullback_fromSpec_app_rank (subStr A B y) hW hV) P
  rw [h3] at e
  rw [← Scheme.Hom.finrank_SpecMap_algebraMap]
  exact e

end GlobalTheory.HilbAff
