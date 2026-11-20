import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafHIPf

/- English proof (translation)
Introduce `n`. Establish `: (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n`. Use function extensionality and compare the values at `x`. Conclude with `pull_comp R f g F n x`. Rewrite using `[this]`.

Conclude with `(hf n).comp (hg n)`.
-/
theorem eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n := by
    funext x; exact pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

/- English proof (translation)
Introduce `n`. Use `Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun y => ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[← pull_comp, e.inv_hom_id, pull_id]`. Rewrite using `[← pull_comp, e.hom_inv_id, pull_id]`.
-/
theorem eqv_iso {R : Type} [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun y => ?_, fun y => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

/- English proof (translation)
The claim follows from `eqv_iso (sch.mapIso (asIso a)) F`.
-/
theorem eqv_isIso {R : Type} [CommRing R] {X Y : Scheme.{0}} (a : X ⟶ Y) [IsIso a] (F : Shv R) :
    Eqv R (sch.map a) F :=
  eqv_iso (sch.mapIso (asIso a)) F

/- English proof (translation)
Rewrite using `[Functor.map_comp]`. Conclude with `eqv_comp _ _ F ha hb`.
-/
theorem eqvS {R : Type} [CommRing R] {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (F : Shv R)
    (ha : Eqv R (sch.map a) F) (hb : Eqv R (sch.map b) F) : Eqv R (sch.map (a ≫ b)) F := by
  rw [Functor.map_comp]; exact eqv_comp _ _ F ha hb

def polyEquiv (A : Type) [CommRing A] : MvPolynomial (Fin 1) A ≃ₐ[A] Polynomial A :=
  MvPolynomial.uniqueAlgEquiv A (Fin 1)

/- English proof (translation)
Establish `h` using `AffineSpace.SpecIso_inv_over (n := Fin 1) (CommRingCat.of A)`. Establish `e : CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A) ≫ CommRingCat.ofHom (polyEquiv A).symm.toRingEquiv.toRingHom = CommRingCat.ofHom (MvPolynomial.C : A →+* MvPolynomial (Fin 1) A)`. Rewrite using `[← CommRingCat.ofHom_comp]`. Conclude with `congrArg _ (RingHom.ext fun a => (polyEquiv A).symm.commutes a)`. Rewrite using `[(Iso.inv_comp_eq _).1 h, Category.assoc, ← Spec.map_comp]`.

Use `erw [e]`.
-/
theorem over_eq (A : Type) [CommRing A] :
    (𝔸(Fin 1; Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A)) =
      ((AffineSpace.SpecIso (Fin 1) (CommRingCat.of A)).hom ≫
        Spec.map (CommRingCat.ofHom (polyEquiv A).symm.toRingEquiv.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) := by
  have h := AffineSpace.SpecIso_inv_over (n := Fin 1) (CommRingCat.of A)
  have e : CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A) ≫
      CommRingCat.ofHom (polyEquiv A).symm.toRingEquiv.toRingHom =
      CommRingCat.ofHom (MvPolynomial.C : A →+* MvPolynomial (Fin 1) A) := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg _ (RingHom.ext fun a => (polyEquiv A).symm.commutes a)
  rw [(Iso.inv_comp_eq _).1 h, Category.assoc, ← Spec.map_comp]
  erw [e]

/- English proof (translation)
Substitute `hk` using the available equality. Establish `P` using `AffineSpace.isPullback_map (n := Fin 1) s`. Establish `hsnd : pullback.snd (𝔸(Fin 1; X) ↘ X) s = P.isoPullback.inv ≫ (((AffineSpace.SpecIso (Fin 1) (CommRingCat.of A)).hom ≫ Spec.map (CommRingCat.ofHom (polyEquiv A).symm.toRingEquiv.toRingHom)) ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))` using `((Iso.eq_inv_comp _).2 P.isoPullback_hom_snd).trans (congrArg (P.isoPullback.inv ≫ ·) (over_eq A))`. Establish `hgeq : g = pullback.snd (𝔸(Fin 1; X) ↘ X) s ≫ inv (pullback.snd (𝟙 X) s)`. Rewrite using `[← hg, Category.assoc, IsIso.hom_inv_id, Category.comp_id]`.

Establish `hI : IsIso (CommRingCat.ofHom (polyEquiv A).symm.toRingEquiv.toRingHom)` using `(polyEquiv A).symm.toRingEquiv.toCommRingCatIso.isIso_hom`. Rewrite using `[hgeq, hsnd]`. Conclude with `eqvS _ _ F (eqvS _ _ F (eqv_isIso _ F) (eqvS _ _ F (eqvS _ _ F (eqv_isIso _ F) (eqv_isIso _ F)) hC)) (eqv_isIso _ F)`.
-/
theorem step {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) (A : Type) [CommRing A]
    (s : Spec (CommRingCat.of A) ⟶ X) (k : 𝔸(Fin 1; X) ⟶ X) (hk : k = 𝔸(Fin 1; X) ↘ X)
    (g : pullback k s ⟶ pullback (𝟙 X) s) (hg : g ≫ pullback.snd _ _ = pullback.snd _ _)
    (hC : Eqv R (spMap (Polynomial.C : A →+* Polynomial A)) F) : Eqv R (sch.map g) F := by
  subst hk
  have P := AffineSpace.isPullback_map (n := Fin 1) s
  have hsnd : pullback.snd (𝔸(Fin 1; X) ↘ X) s = P.isoPullback.inv ≫ (((AffineSpace.SpecIso (Fin 1) (CommRingCat.of A)).hom ≫
        Spec.map (CommRingCat.ofHom (polyEquiv A).symm.toRingEquiv.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) :=
    ((Iso.eq_inv_comp _).2 P.isoPullback_hom_snd).trans (congrArg (P.isoPullback.inv ≫ ·) (over_eq A))
  have hgeq : g = pullback.snd (𝔸(Fin 1; X) ↘ X) s ≫ inv (pullback.snd (𝟙 X) s) := by
    rw [← hg, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hI : IsIso (CommRingCat.ofHom (polyEquiv A).symm.toRingEquiv.toRingHom) :=
    (polyEquiv A).symm.toRingEquiv.toCommRingCatIso.isIso_hom
  rw [hgeq, hsnd]
  exact eqvS _ _ F (eqvS _ _ F (eqv_isIso _ F) (eqvS _ _ F (eqvS _ _ F (eqv_isIso _ F) (eqv_isIso _ F)) hC))
    (eqv_isIso _ F)

/- English proof (translation)
Introduce `b3 c4 q _ i X hq`. Use `b3 q (𝔸(Fin 1; X) ↘ X) (𝟙 X) hq i (fun A _ s _ => ?_)` and prove the remaining obligations. Establish `hqA : IsUnit (q : A)`. Simplify using `using hq.map (s.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom`. Conclude with `step _ X A s _ (Category.comp_id _) _ ((pullback.lift_snd _ _ _).trans (Category.comp_id _)) (c4 q A hqA i)`.
-/
theorem LeafHI_of : LateralTheory.E.t_E6Cut.LeafHI := by
  intro b3 c4 q _ i X hq
  refine b3 q (𝔸(Fin 1; X) ↘ X) (𝟙 X) hq i (fun A _ s _ => ?_)
  have hqA : IsUnit (q : A) := by
    simpa using hq.map (s.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom
  exact step _ X A s _ (Category.comp_id _) _ ((pullback.lift_snd _ _ _).trans (Category.comp_id _)) (c4 q A hqA i)

end LateralTheory.E.LeafHIPf
