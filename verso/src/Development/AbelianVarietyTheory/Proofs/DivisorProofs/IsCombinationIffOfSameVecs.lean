import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

/- English proof (translation)
Substitute `hy` using the available equality. Take `rfl : U = fun k => V k ≫ φ` from `funext fun k => (hU k).symm`. Take `⟨e, he⟩` from `LiePull.exists_pushEquiv h (FramedFlatCoordinates.epsAt x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f) (Category.assoc _ _ _).symm`. Take `rfl : w' = e w` from `Over.OverMorphism.ext (hw.symm.trans (he _).symm)`. Establish `sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R))` using `fun c => by`.

Use `(Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)` and prove the remaining obligations. Apply the tactic sequence `ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]`. Establish `hR : ∀ (k : Fin n) (u : FramedFlatCoordinates.epsAt x ⟶ G'), u.left = spMap (epsScaleR (a k)) ≫ V k ↔ (e u).left = spMap (epsScaleR (a k)) ≫ V k ≫ φ` using `fun k u => by`. Rewrite using `[he]`. Use `⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩` and prove the remaining obligations.

Use `(Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))` and prove the remaining obligations. Use `(congrArg (spMap (epsScaleR (a k)) ≫ ·) (hV k)).trans ?_` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc (a k)))`. Establish `pr : ∀ u : Fin n → (FramedFlatCoordinates.epsAt x ⟶ G'), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod` using `fun u => by rw [map_list_prod, List.map_ofFn]; rfl`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `⟨fun i => e (u i), fun i => (hR _ _).1 (hu i), pr u⟩`. Introduce and unpack `⟨u, hu, hw⟩`. Use `⟨fun i => e.symm (u i), fun i => (hR _ _).2 (by rw [e.apply_symm_apply]; exact hu i), e.injective ?_⟩` and prove the remaining obligations. Rewrite using `[pr]`.

Simplify using `only [MulEquiv.apply_symm_apply]`. Conclude with `hw`.
-/
theorem isCombination_pull_iff {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x : Sp R ⟶ S') (y : Sp R ⟶ S)
    (hy : y = x ≫ f) {n : ℕ} (a : Fin n → R) (V : Fin n → (Sp (DualNumber R) ⟶ G'.left))
    (hV : ∀ k, V k ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x)
    (U : Fin n → (Sp (DualNumber R) ⟶ G.left)) (hU : ∀ k, V k ≫ φ = U k)
    (w : FramedFlatCoordinates.epsAt x ⟶ G') (w' : FramedFlatCoordinates.epsAt y ⟶ G) (hw : w.left ≫ φ = w'.left) :
    FramedFlatCoordinates.IsCombination x a V w ↔ FramedFlatCoordinates.IsCombination y a U w' := by
  subst hy
  obtain rfl : U = fun k => V k ≫ φ := funext fun k => (hU k).symm
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (FramedFlatCoordinates.epsAt x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain rfl : w' = e w := Over.OverMorphism.ext (hw.symm.trans (he _).symm)
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (k : Fin n) (u : FramedFlatCoordinates.epsAt x ⟶ G'), u.left = spMap (epsScaleR (a k)) ≫ V k ↔
      (e u).left = spMap (epsScaleR (a k)) ≫ V k ≫ φ := fun k u => by
    rw [he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR (a k)) ≫ ·) (hV k)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc (a k)))
  have pr : ∀ u : Fin n → (FramedFlatCoordinates.epsAt x ⟶ G'), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod :=
    fun u => by rw [map_list_prod, List.map_ofFn]; rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => e (u i), fun i => (hR _ _).1 (hu i), pr u⟩
  · rintro ⟨u, hu, hw⟩
    refine ⟨fun i => e.symm (u i), fun i => (hR _ _).2 (by rw [e.apply_symm_apply]; exact hu i), e.injective ?_⟩
    rw [pr]
    simp only [MulEquiv.apply_symm_apply]
    exact hw

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y R R' _ _ g x x' n v vb v' vb' hx h h' a i`. Use `choose v₁ h₁ h₂ using h`. Take `⟨w, hw₁, hw₂⟩` from `h' i`. Establish `hV : ∀ k, (spMap (Chart.dualMapR g) ≫ (v₁ k).left) ≫ Y.oF.t.G.hom = spMap (algebraMap R' (DualNumber R')) ≫ x'` using `fun k => by`. Substitute `hx` using the available equality.

Conclude with `Over.w (DetExtendZero.epsMap g x ≫ v₁ k)`. Use `(isCombination_pull_iff Y.m0.toSABMap.cart x' _ rfl a _ hV _ (fun k => ?_) w _ hw₁).symm.trans (isCombination_pull_iff Y.m.cart x' _ (Category.assoc _ _ _) a _ hV _ (fun k => ?_) w _ hw₂)` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).trans (congrArg (spMap (Chart.dualMapR g) ≫ ·) (h₁ k))`. Conclude with `(Category.assoc _ _ _).trans (congrArg (spMap (Chart.dualMapR g) ≫ ·) (h₂ k))`.
-/
theorem isCombination_iff_of_sameVecs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (x : Sp R ⟶ Xo.XF c) (x' : Sp R' ⟶ Xo.XF c) (n : ℕ) (v : Fin n → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)) (vb : Fin n → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)) (v' : Fin n → (epsAt (x' ≫ toX Xo c) ⟶ Xo.univ.t.G)) (vb' : Fin n → (epsAt ((x' ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)), x' = spMap g ≫ x → SameVecs Y x v vb → SameVecs Y x' v' vb' → ∀ (a : Fin n → R') (i : Fin n), FramedFlatCoordinates.IsCombination (x' ≫ toX Xo c) a (fun k => spMap (Chart.dualMapR g) ≫ (v k).left) (v' i) ↔ FramedFlatCoordinates.IsCombination ((x' ≫ Y.jQ) ≫ genι Y) a (fun k => spMap (Chart.dualMapR g) ≫ (vb k).left) (vb' i) := by
  intro E _ _ _ H D l Xo c O _ β Y R R' _ _ g x x' n v vb v' vb' hx h h' a i
  choose v₁ h₁ h₂ using h
  obtain ⟨w, hw₁, hw₂⟩ := h' i
  have hV : ∀ k, (spMap (Chart.dualMapR g) ≫ (v₁ k).left) ≫ Y.oF.t.G.hom =
      spMap (algebraMap R' (DualNumber R')) ≫ x' := fun k => by
    subst hx
    exact Over.w (DetExtendZero.epsMap g x ≫ v₁ k)
  refine (isCombination_pull_iff Y.m0.toSABMap.cart x' _ rfl a _ hV _ (fun k => ?_) w _ hw₁).symm.trans
    (isCombination_pull_iff Y.m.cart x' _ (Category.assoc _ _ _) a _ hV _ (fun k => ?_) w _ hw₂)
  · exact (Category.assoc _ _ _).trans (congrArg (spMap (Chart.dualMapR g) ≫ ·) (h₁ k))
  · exact (Category.assoc _ _ _).trans (congrArg (spMap (Chart.dualMapR g) ≫ ·) (h₂ k))

end GlobalTheory.DetLine
