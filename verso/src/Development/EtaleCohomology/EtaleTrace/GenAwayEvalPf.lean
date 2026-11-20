import Development.EtaleCohomology.EtaleTrace.GenInPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov.GenInPf

variable {k : Type} [Field k] {N : ℕ}

/- English proof (translation)
Rewrite using `[IsAffineOpen.fromSpec, Iso.inv_comp_eq, Proj.awayι, ← Category.assoc, ← Category.assoc]`. Establish `e : (Proj.isAffineOpen_basicOpen (A k N) f hf hd).isoSpec.hom ≫ Spec.map (Proj.awayToSection (A k N) f) = (Proj.basicOpenIsoSpec (A k N) f hf hd).hom`. Rewrite using `[Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec, IsAffineOpen.isoSpec_hom]`. Rewrite using `[e, Iso.hom_inv_id, Category.id_comp]`.
-/
theorem fromSpec_eq {f : MvPolynomial (Fin (N + 1)) k} {d : ℕ} (hf : f ∈ A k N d) (hd : 0 < d) :
    (Proj.isAffineOpen_basicOpen (A k N) f hf hd).fromSpec =
      Spec.map (Proj.awayToSection (A k N) f) ≫ Proj.awayι (A k N) f hf hd := by
  rw [IsAffineOpen.fromSpec, Iso.inv_comp_eq, Proj.awayι, ← Category.assoc, ← Category.assoc]
  have e : (Proj.isAffineOpen_basicOpen (A k N) f hf hd).isoSpec.hom ≫ Spec.map (Proj.awayToSection (A k N) f) =
      (Proj.basicOpenIsoSpec (A k N) f hf hd).hom := by
    rw [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec, IsAffineOpen.isoSpec_hom]
  rw [e, Iso.hom_inv_id, Category.id_comp]

/- English proof (translation)
Establish `hU` using `Proj.isAffineOpen_basicOpen (A k N) f hf hd`. Establish `key : hU.fromSpec ≫ Proj.toSpecZero (A k N) = Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫ Proj.awayToSection (A k N) f)`. Rewrite using `[fromSpec_eq hf hd, Category.assoc, Proj.awayι_toSpecZero, Spec.map_comp]`. Establish `h1 : (Proj.toSpecZero (A k N)).appLE ⊤ (Proj.basicOpen (A k N) f) le_top ≫ hU.fromSpec.appLE _ ⊤ hU.fromSpec_preimage_self.ge = (hU.fromSpec ≫ Proj.toSpecZero (A k N)).appLE ⊤ ⊤ (by simp)` using `Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _`. Simplify using `only [key] at h1`.

Establish `h3 : hU.fromSpec.appLE _ ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv`. Rewrite using `[Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]`. Conclude with `(congrArg (_ ≫ ·) ((congrArg _ (Subsingleton.elim _ (𝟙 _))).trans ((Spec _).presheaf.map_id _))).trans (Category.comp_id _)`. Establish `h4 : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S) e, (Spec.map g).appLE ⊤ ⊤ e = (Spec.map g).appTop` using `fun _ _ => rfl`. Rewrite `h1` using `[h3, h4]`.

Rewrite using `[← cancel_mono (Scheme.ΓSpecIso _).inv, Category.assoc, h1, Scheme.ΓSpecIso_inv_naturality]`.
-/
theorem constSecC {f : MvPolynomial (Fin (N + 1)) k} {d : ℕ} (hf : f ∈ A k N d) (hd : 0 < d) :
    (Scheme.ΓSpecIso (CommRingCat.of (A k N 0))).inv ≫
      (Proj.toSpecZero (A k N)).appLE ⊤ (Proj.basicOpen (A k N) f) le_top =
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫ Proj.awayToSection (A k N) f := by
  have hU := Proj.isAffineOpen_basicOpen (A k N) f hf hd
  have key : hU.fromSpec ≫ Proj.toSpecZero (A k N) =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫ Proj.awayToSection (A k N) f) := by
    rw [fromSpec_eq hf hd, Category.assoc, Proj.awayι_toSpecZero, Spec.map_comp]
  have h1 : (Proj.toSpecZero (A k N)).appLE ⊤ (Proj.basicOpen (A k N) f) le_top ≫
      hU.fromSpec.appLE _ ⊤ hU.fromSpec_preimage_self.ge =
      (hU.fromSpec ≫ Proj.toSpecZero (A k N)).appLE ⊤ ⊤ (by simp) := Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  simp only [key] at h1
  have h3 : hU.fromSpec.appLE _ ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg (_ ≫ ·) ((congrArg _ (Subsingleton.elim _ (𝟙 _))).trans ((Spec _).presheaf.map_id _))).trans
      (Category.comp_id _)
  have h4 : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S) e, (Spec.map g).appLE ⊤ ⊤ e = (Spec.map g).appTop := fun _ _ => rfl
  rw [h3, h4] at h1
  rw [← cancel_mono (Scheme.ΓSpecIso _).inv, Category.assoc, h1, Scheme.ΓSpecIso_inv_naturality]

/- English proof (translation)
Substitute `hp` using the available equality. Establish `hC` using `constSecC (X_mem k N i) one_pos`. Establish `e1 : kHom (ι ≫ PNto k N) = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top ≫ X.presheaf.germ _ (genericPoint X) h).hom`. Rewrite using `[kHom, ← X.presheaf.germ_res (homOfLE (le_top : ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i) ≤ ⊤)) _ h]`. Both sides reduce to the same expression.

Establish `e2 : (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top = (PNto k N).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top ≫ ι.appLE (Proj.basicOpen (A k N) (MvPolynomial.X i)) _ le_rfl` using `(Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm`. Establish `e3 : (PNto k N).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top = (Spec.map (CommRingCat.ofHom (algebraMap k (A k N 0)))).appTop ≫ (Proj.toSpecZero (A k N)).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top` using `Scheme.Hom.comp_appLE _ _ _ _ _`. Establish `e4 : ι.appLE (Proj.basicOpen (A k N) (MvPolynomial.X i)) _ le_rfl = ι.app _` using `Scheme.Hom.appLE_eq_app _`. Establish `e5 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top = CommRingCat.ofHom (algebraMap k (A k N 0)) ≫ (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫ Proj.awayToSection (A k N) (MvPolynomi …`. Rewrite using `[e2, e3, e4, ← hC]`.

Establish `n` using `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (A k N 0)))`. Simplify using `only [Category.assoc] at n ⊢`. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) n.symm).trans (by simp only [Category.assoc]))`. Rewrite using `[e1, ← Category.assoc, e5]`. Both sides reduce to the same expression.
-/
theorem kHom_eq {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (ι : X ⟶ PN k N) (hp : ι ≫ PNto k N = p)
    (i : Fin (N + 1)) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) (c : k) :
    kHom p c = X.presheaf.germ _ (genericPoint X) h ((ι.app _).hom ((Proj.awayToSection (A k N) (MvPolynomial.X i)).hom
      (HomogeneousLocalization.fromZeroRingHom _ _ (algebraMap k (A k N 0) c)))) := by
  subst hp
  have hC := constSecC (X_mem k N i) one_pos
  have e1 : kHom (ι ≫ PNto k N) = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top ≫
      X.presheaf.germ _ (genericPoint X) h).hom := by
    rw [kHom, ← X.presheaf.germ_res (homOfLE (le_top : ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i) ≤ ⊤)) _ h]
    rfl
  have e2 : (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top =
      (PNto k N).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top ≫
        ι.appLE (Proj.basicOpen (A k N) (MvPolynomial.X i)) _ le_rfl :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e3 : (PNto k N).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top =
      (Spec.map (CommRingCat.ofHom (algebraMap k (A k N 0)))).appTop ≫
        (Proj.toSpecZero (A k N)).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top :=
    Scheme.Hom.comp_appLE _ _ _ _ _
  have e4 : ι.appLE (Proj.basicOpen (A k N) (MvPolynomial.X i)) _ le_rfl = ι.app _ := Scheme.Hom.appLE_eq_app _
  have e5 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top =
      CommRingCat.ofHom (algebraMap k (A k N 0)) ≫ (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫
        Proj.awayToSection (A k N) (MvPolynomial.X i)) ≫ ι.app _ := by
    rw [e2, e3, e4, ← hC]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (A k N 0)))
    simp only [Category.assoc] at n ⊢
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) n.symm).trans (by simp only [Category.assoc]))
  rw [e1, ← Category.assoc, e5]
  rfl

/- English proof (translation)
Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`. Rewrite using `[← coe_eval₂Hom, map_sum, ← coe_eval₂Hom, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Establish `hd` using `hg (mem_support_iff.mp hs)`.

Simplify using `only [coe_eval₂Hom, eval₂_monomial, Finsupp.prod]`. Rewrite using `[mul_assoc]`. Use `congr 1`. Establish `hm : m = ∑ j ∈ s.support, s j`. Rewrite using `[← hd]`.

Simplify using `[Finsupp.weight_apply, Finsupp.sum]`. Rewrite using `[hm, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun j _ => by rw [← mul_pow, hab]`.
-/
theorem eval₂_mul_pow {σ R L : Type} [CommSemiring R] [CommRing L] (F : R →+* L) (a b : σ → L) (t : L)
    (hab : ∀ j, a j * t = b j) {m : ℕ} {g : MvPolynomial σ R} (hg : g.IsHomogeneous m) :
    eval₂ F a g * t ^ m = eval₂ F b g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [← coe_eval₂Hom, map_sum, ← coe_eval₂Hom, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := hg (mem_support_iff.mp hs)
  simp only [coe_eval₂Hom, eval₂_monomial, Finsupp.prod]
  rw [mul_assoc]
  congr 1
  have hm : m = ∑ j ∈ s.support, s j := by
    rw [← hd]
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [hm, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by rw [← mul_pow, hab]

/- English proof (translation)
Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Set `vH : HomogeneousLocalization (A k N) (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k)) →+* Localization (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k))` to `{ toFun := fun y => y.val, map_one' := HomogeneousLocalization.val_one, map_mul' := HomogeneousLocalization.val_mul, map_zero' := HomogeneousLocalization.val_zero, map_add' := HomogeneousLocalization.val_add }`. Express the relevant statement in the definitionally equal form `_ = vH _`. Rewrite using `[eval₂_comp_left]`. Establish `hgh : g.IsHomogeneous m` using `by simpa using (mem_homogeneousSubmodule _ _).1 hg`.

Use `set L := Localization (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k))`. Establish `hF : vH.comp ((HomogeneousLocalization.fromZeroRingHom (A k N) _).comp (algebraMap k (A k N 0))) = (algebraMap (MvPolynomial (Fin (N + 1)) k) L).comp C`. Use extensionality with `c`. Simplify using `[vH, HomogeneousLocalization.fromZeroRingHom]`. Both sides reduce to the same expression.

Establish `hab : ∀ j, (vH ∘ fun j => HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) 1 (X j) (X_mem' k N j)) j * algebraMap (MvPolynomial (Fin (N + 1)) k) L (X i) = algebraMap (MvPolynomial (Fin (N + 1)) k) L (X j)`. Introduce `j`. Simplify using `only [Function.comp_apply, vH, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']`. Simplify using `only [pow_one]`. Conclude with `IsLocalization.mk'_spec _ _ _`.

Establish `key` using `eval₂_mul_pow ((algebraMap (MvPolynomial (Fin (N + 1)) k) L).comp C) _ _ _ hab hgh`. Rewrite using `[hF, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]`. Express the relevant statement in the definitionally equal form `_ = _ * algebraMap (MvPolynomial (Fin (N + 1)) k) L (X i ^ m)`. Rewrite using `[map_pow, key]`. Conclude with `(congrArg _ (eval₂_eta g)).symm.trans (eval₂_comp_left _ _ _ _)`.
-/
theorem mk_eq_eval (i : Fin (N + 1)) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • 1)) :
    HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) m g hg =
      eval₂ ((HomogeneousLocalization.fromZeroRingHom (A k N) _).comp (algebraMap k (A k N 0)))
        (fun j => HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) 1 (X j) (X_mem' k N j)) g := by
  apply HomogeneousLocalization.val_injective
  let vH : HomogeneousLocalization (A k N) (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k)) →+*
      Localization (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k)) :=
    { toFun := fun y => y.val, map_one' := HomogeneousLocalization.val_one,
      map_mul' := HomogeneousLocalization.val_mul, map_zero' := HomogeneousLocalization.val_zero,
      map_add' := HomogeneousLocalization.val_add }
  change _ = vH _
  rw [eval₂_comp_left]
  have hgh : g.IsHomogeneous m := by simpa using (mem_homogeneousSubmodule _ _).1 hg
  set L := Localization (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k))
  have hF : vH.comp ((HomogeneousLocalization.fromZeroRingHom (A k N) _).comp (algebraMap k (A k N 0))) =
      (algebraMap (MvPolynomial (Fin (N + 1)) k) L).comp C := by
    ext c
    simp [vH, HomogeneousLocalization.fromZeroRingHom]
    rfl
  have hab : ∀ j, (vH ∘ fun j => HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) 1 (X j) (X_mem' k N j)) j *
      algebraMap (MvPolynomial (Fin (N + 1)) k) L (X i) = algebraMap (MvPolynomial (Fin (N + 1)) k) L (X j) := by
    intro j
    simp only [Function.comp_apply, vH, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
    simp only [pow_one]
    exact IsLocalization.mk'_spec _ _ _
  have key := eval₂_mul_pow ((algebraMap (MvPolynomial (Fin (N + 1)) k) L).comp C) _ _ _ hab hgh
  rw [hF, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  change _ = _ * algebraMap (MvPolynomial (Fin (N + 1)) k) L (X i ^ m)
  rw [map_pow, key]
  exact (congrArg _ (eval₂_eta g)).symm.trans (eval₂_comp_left _ _ _ _)

/- English proof (translation)
Introduce `k _ X _ p N ι hp i h m g hg`. Set `φ : HomogeneousLocalization.Away (A k N) (MvPolynomial.X i) →+* X.functionField` to `(X.presheaf.germ _ (genericPoint X) h).hom.comp ((ι.app _).hom.comp (Proj.awayToSection (A k N) (MvPolynomial.X i)).hom)`. Establish `e : away ι (MvPolynomial.X i) (X_mem k N i) h m g hg = φ (HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) m g hg)` using `rfl`. Rewrite using `[e, mk_eq_eval, eval₂_comp_left]`. Use `congr 1`.

Use extensionality with `c`. Conclude with `(kHom_eq p ι hp i h c).symm`.
-/
theorem GenAwayEval_of : GenAwayEval := by
  intro k _ X _ p N ι hp i h m g hg
  let φ : HomogeneousLocalization.Away (A k N) (MvPolynomial.X i) →+* X.functionField :=
    (X.presheaf.germ _ (genericPoint X) h).hom.comp
      ((ι.app _).hom.comp (Proj.awayToSection (A k N) (MvPolynomial.X i)).hom)
  have e : away ι (MvPolynomial.X i) (X_mem k N i) h m g hg =
      φ (HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) m g hg) := rfl
  rw [e, mk_eq_eval, eval₂_comp_left]
  congr 1
  ext c
  exact (kHom_eq p ι hp i h c).symm

end LateralTheory.EtaleTrace.Cov.GenInPf
