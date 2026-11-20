import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTorusExtensionPointOfGroupPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

section Kernel

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B T : Over S} {G' : Over S'} [GrpObj B] [GrpObj G']
  {X : Type} [AddCommGroup X]

/- English proof (translation)
Establish `: Mono Q.i` using `⟨fun _ _ h => Q.isKernel.hom_ext h (toUnit_unique _ _)⟩`. Use `infer_instance`.
-/
theorem TQ.mono_i_left (Q : TQ G' X) : Mono Q.i.left := by
  have : Mono Q.i := ⟨fun _ _ h => Q.isKernel.hom_ext h (toUnit_unique _ _)⟩
  infer_instance

/- English proof (translation)
Take `⟨eB, heB⟩` from `GlobalTheory.exists_mulEquiv_of_isGrpPullback hB _ _ hc`. Set `R : Over.mk (r ≫ T.hom) ⟶ T` to `Over.homMk r rfl`. Set `xe' : Over.mk (xe ≫ G'.hom) ⟶ G'` to `Over.homMk xe rfl`. Establish `e₁ : (eB (xe' ≫ Q.q)).left = xe ≫ Q.q.left ≫ β` using `(heB _).trans (Category.assoc _ _ _)`. Establish `e₂ : (eB 1).left = r ≫ (1 : T ⟶ B).left`.

Rewrite using `[map_one, ← MonObj.comp_one R]`. Both sides reduce to the same expression. Rewrite using `[← e₁, ← e₂]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h₁ : xe' ≫ Q.q = toUnit _ ≫ η[Q.B]` using `eB.injective (Over.OverMorphism.ext h)`. Conclude with `⟨(Q.isKernel.lift _ _ h₁).left, congrArg (fun z => z.left) (Q.isKernel.lift_fst _ _ h₁)⟩`. Introduce and unpack `⟨τ, hτ⟩`. Set `τ' : Over.mk (xe ≫ G'.hom) ⟶ splitTorus S' X` to `Over.homMk τ (by`. Rewrite using `[← hτ, ← Over.w Q.i]`.

Conclude with `(Category.assoc _ _ _).symm)`. Establish `h₁ : τ' ≫ Q.i = xe'` using `Over.OverMorphism.ext hτ`. Establish `h₂ : xe' ≫ Q.q = 1`. Rewrite using `[← h₁, Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (τ' ≫ toUnit _)]`. Rewrite using `[h₂]`.
-/
theorem TQ.image_eq_one_iff (Q : TQ G' X) {β : Q.B.left ⟶ B.left} (hB : IsGrpPullback Q.B B f β)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (xe : Z ⟶ G'.left) (hc : r ≫ T.hom = (xe ≫ G'.hom) ≫ f) :
    xe ≫ Q.q.left ≫ β = r ≫ (1 : T ⟶ B).left ↔ ∃ τ : Z ⟶ (splitTorus S' X).left, τ ≫ Q.i.left = xe := by
  obtain ⟨eB, heB⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hB _ _ hc
  let R : Over.mk (r ≫ T.hom) ⟶ T := Over.homMk r rfl
  let xe' : Over.mk (xe ≫ G'.hom) ⟶ G' := Over.homMk xe rfl
  have e₁ : (eB (xe' ≫ Q.q)).left = xe ≫ Q.q.left ≫ β := (heB _).trans (Category.assoc _ _ _)
  have e₂ : (eB 1).left = r ≫ (1 : T ⟶ B).left := by
    rw [map_one, ← MonObj.comp_one R]; rfl
  rw [← e₁, ← e₂]
  constructor
  · intro h
    have h₁ : xe' ≫ Q.q = toUnit _ ≫ η[Q.B] := eB.injective (Over.OverMorphism.ext h)
    exact ⟨(Q.isKernel.lift _ _ h₁).left, congrArg (fun z => z.left) (Q.isKernel.lift_fst _ _ h₁)⟩
  · rintro ⟨τ, hτ⟩
    let τ' : Over.mk (xe ≫ G'.hom) ⟶ splitTorus S' X := Over.homMk τ (by
      rw [← hτ, ← Over.w Q.i]; exact (Category.assoc _ _ _).symm)
    have h₁ : τ' ≫ Q.i = xe' := Over.OverMorphism.ext hτ
    have h₂ : xe' ≫ Q.q = 1 := by
      rw [← h₁, Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (τ' ≫ toUnit _)]
    rw [h₂]

end Kernel

section Scal

variable {A C : Type} [CommRing A] [CommRing C] {Y Y' : Scheme.{0}}

noncomputable def scalRingHom (p : Y ⟶ Spec (CommRingCat.of A)) : A →+* Γ(Y, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop).hom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem scalRingHom_apply (p : Y ⟶ Spec (CommRingCat.of A)) (a : A) : scalRingHom p a = scal p a := rfl

/- English proof (translation)
The claim follows from `congrArg CommRingCat.Hom.hom (SplitTorusPoints.ΓSpecIso_inv_comp_specMap p (CommRingCat.ofHom φ))`.
-/
theorem scalRingHom_specMap (p : Y ⟶ Spec (CommRingCat.of C)) (φ : A →+* C) :
    scalRingHom (p ≫ Spec.map (CommRingCat.ofHom φ)) = (scalRingHom p).comp φ :=
  congrArg CommRingCat.Hom.hom (SplitTorusPoints.ΓSpecIso_inv_comp_specMap p (CommRingCat.ofHom φ))

/- English proof (translation)
Use `⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J (scalRingHom r) fun _ ha => RingHom.mem_ker.1 (h ha))), ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]`. Apply `ext_to_Spec` to reduce the goal to its premises. Use `(SplitTorusPoints.ΓSpecIso_inv_comp_specMap _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]`.

Both sides reduce to the same expression.
-/
theorem exists_factor_quotient (r : Y ⟶ Spec (CommRingCat.of C)) (J : Ideal C)
    (h : J ≤ RingHom.ker (scalRingHom r)) :
    ∃ r' : Y ⟶ Spec (CommRingCat.of (C ⧸ J)), r' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = r := by
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J (scalRingHom r) fun _ ha => RingHom.mem_ker.1 (h ha))), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]
  apply ext_to_Spec
  refine (SplitTorusPoints.ΓSpecIso_inv_comp_specMap _ _).trans ?_
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  rfl

/- English proof (translation)
Use `exists_factor_quotient r _ ?_` and prove the remaining obligations. Rewrite using `[← Ideal.map_pow, Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Use `congrArg (fun q => scalRingHom q a) h` as an intermediate fact. Simplify using `only [scalRingHom_specMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero] at this`.

Conclude with `this.symm`.
-/
theorem exists_factor_thick (φ : A →+* C) (I : Ideal A) (e : ℕ) (r : Y ⟶ Spec (CommRingCat.of C))
    (p : Y ⟶ Spec (CommRingCat.of (A ⧸ I ^ (e + 1))))
    (h : p ≫ thick A I e = r ≫ Spec.map (CommRingCat.ofHom φ)) :
    ∃ r' : Y ⟶ Spec (CommRingCat.of (C ⧸ I.map φ ^ (e + 1))), r' ≫ thick C (I.map φ) e = r := by
  refine exists_factor_quotient r _ ?_
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro a ha
  have := congrArg (fun q => scalRingHom q a) h
  simp only [scalRingHom_specMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero] at this
  exact this.symm

/- English proof (translation)
Take `⟨τ, hτ⟩` from `(splitTorusPointsEquiv S X (Over.mk p)).surjective ((Units.map (scalRingHom r).toMonoidHom).comp c)`. Use `⟨τ.left, Over.w τ, fun χ => ?_⟩` and prove the remaining obligations. Use `(splitTorusPointsEquiv_val S X _ τ χ).symm.trans ?_` and prove the remaining obligations. Rewrite using `[hτ]`. Both sides reduce to the same expression.
-/
theorem exists_torus_point {S : Scheme.{0}} {X : Type} [AddCommGroup X] (c : Multiplicative X →* Cˣ)
    (r : Y ⟶ Spec (CommRingCat.of C)) (p : Y ⟶ S) : ∃ τ : Y ⟶ (splitTorus S X).left, τ ≫ (splitTorus S X).hom = p ∧
      ∀ χ, τ.appTop.hom (charUnit S X χ).val = scal r (c (Multiplicative.ofAdd χ)).val := by
  obtain ⟨τ, hτ⟩ := (splitTorusPointsEquiv S X (Over.mk p)).surjective
    ((Units.map (scalRingHom r).toMonoidHom).comp c)
  refine ⟨τ.left, Over.w τ, fun χ => ?_⟩
  refine (splitTorusPointsEquiv_val S X _ τ χ).symm.trans ?_
  rw [hτ]; rfl

/- English proof (translation)
Set `u` to `fun e => splitTorusPointsEquiv (S e) X (Over.mk (τ e ≫ (splitTorus (S e) X).hom)) (Over.homMk (τ e) rfl)`. Establish `hu : ∀ e χ, (u e (Multiplicative.ofAdd χ)).val = (τ e).appTop.hom (charUnit _ X χ).val` using `fun e χ => splitTorusPointsEquiv_val _ _ _ _ χ`. Use `choose b hb using fun χ : X => CompletePoint.exists_fn_of_thick J (fun e => (τ e).appTop.hom (charUnit _ X χ).val) fun e => by rw [← h e χ, Scheme.Hom.comp_appTop]; rfl`. Set `b' : Multiplicative X →* Γ(Spec (CommRingCat.of C), ⊤)` to `{ toFun := fun χ => b χ.toAdd map_one' := CompletePoint.fn_eq_of_thick J fun e => by`. Rewrite using `[hb, ← hu]`.

Conclude with `(congrArg Units.val (map_one (u e))).trans (map_one _).symm`. Use the proof step `map_mul' := fun χ χ' => CompletePoint.fn_eq_of_thick J fun e => by`. Rewrite using `[(thick C J e).appTop.hom.map_mul, hb, hb, hb, ← hu, ← hu, ← hu]`. Conclude with `congrArg Units.val (map_mul (u e) χ χ') }`. Use `⟨((Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom.toMonoidHom.comp b').toHomUnits, fun e χ => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hb]`. Conclude with `congrArg (thick C J e).appTop.hom (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of C)) (b χ)).symm`.
-/
theorem exists_hom_of_thick {X : Type} [AddCommGroup X] (J : Ideal C) [IsAdicComplete J C] {S : ℕ → Scheme.{0}}
    (τ : ∀ e, Spec (CommRingCat.of (C ⧸ J ^ (e + 1))) ⟶ (splitTorus (S e) X).left)
    (h : ∀ e χ, (thickTrans C J e ≫ τ (e + 1)).appTop.hom (charUnit _ X χ).val =
      (τ e).appTop.hom (charUnit _ X χ).val) :
    ∃ c : Multiplicative X →* Cˣ, ∀ e χ,
      (τ e).appTop.hom (charUnit _ X χ).val = scal (thick C J e) (c (Multiplicative.ofAdd χ)).val := by
  let u := fun e => splitTorusPointsEquiv (S e) X (Over.mk (τ e ≫ (splitTorus (S e) X).hom)) (Over.homMk (τ e) rfl)
  have hu : ∀ e χ, (u e (Multiplicative.ofAdd χ)).val = (τ e).appTop.hom (charUnit _ X χ).val := fun e χ =>
    splitTorusPointsEquiv_val _ _ _ _ χ
  choose b hb using fun χ : X => CompletePoint.exists_fn_of_thick J (fun e => (τ e).appTop.hom (charUnit _ X χ).val)
    fun e => by rw [← h e χ, Scheme.Hom.comp_appTop]; rfl
  let b' : Multiplicative X →* Γ(Spec (CommRingCat.of C), ⊤) :=
    { toFun := fun χ => b χ.toAdd
      map_one' := CompletePoint.fn_eq_of_thick J fun e => by
        rw [hb, ← hu]; exact (congrArg Units.val (map_one (u e))).trans (map_one _).symm
      map_mul' := fun χ χ' => CompletePoint.fn_eq_of_thick J fun e => by
        rw [(thick C J e).appTop.hom.map_mul, hb, hb, hb, ← hu, ← hu, ← hu]
        exact congrArg Units.val (map_mul (u e) χ χ') }
  refine ⟨((Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom.toMonoidHom.comp b').toHomUnits, fun e χ => ?_⟩
  rw [← hb]
  exact congrArg (thick C J e).appTop.hom (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of C)) (b χ)).symm

end Scal

/- English proof (translation)
Introduce `V _ _ _ A G _ _ s t a W _ _ _ hW _ x`. Set `I` to `IsLocalRing.maximalIdeal V`. Set `φ` to `algebraMap V W`. Establish `hx : x.left ≫ G.hom = Spec.map (CommRingCat.ofHom φ)` using `Over.w x`. Establish `hF : ∀ e, (fstG I e G).left ≫ G.hom = (thickObj V I e G).hom ≫ thick V I e` using `fun e => pullback.condition`.

Establish `mF : ∀ e, Mono (fstG I e G).left` using `fun e => pullback.fst_of_mono (f := G.hom) (g := thick V I e)`. Establish `base : ∀ (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V I e G).left), xe ≫ (fstG I e G).left = r ≫ x.left → r ≫ Spec.map (CommRingCat.ofHom φ) = (xe ≫ (thickObj V I e G).hom) ≫ thick V I e` using `fun e Z r xe h => by`. Rewrite using `[Category.assoc, ← hF, ← hx, ← Category.assoc, ← h]`. Conclude with `Category.assoc _ _ _`. Establish `ker` using `fun (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V I e G).left) (h : xe ≫ (fstG I e G).left = r ≫ x.left) => (t.l e).Q.image_eq_one_iff (T := Over.mk (Spec.map (CommRingCat.ofHom φ))) (a.b_pb e).1 r xe (base e r xe h)`.

Prove the components needed by the constructor for the conclusion. Introduce `H`. Set `J` to `I.map φ`. Establish `hle : ∀ e : ℕ, I ^ (e + 1) ≤ (J ^ (e + 1)).comap φ` using `fun e => by`. Rewrite using `[← Ideal.map_pow]`.

Conclude with `Ideal.le_comap_map`. Establish `hp : ∀ e, (thick W J e ≫ x.left) ≫ G.hom = Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ (hle e))) ≫ thick V I e` using `fun e => by`. Rewrite using `[Category.assoc, hx, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]`. Take `⟨y, hy⟩ : ∃ y : ∀ e, Spec (CommRingCat.of (W ⧸ J ^ (e + 1))) ⟶ (thickObj V I e G).left, ∀ e, y e ≫ (fstG I e G).left = thick W J e ≫ x.left` from `⟨fun e => pullback.lift _ _ (hp e), fun e => pullback.lift_fst _ _ _⟩`. Use `choose τ hτ using fun e => (ker e _ _ (hy e)).1 (H e _ _ _ (hy e))`.

Take `⟨c, hc⟩` from `exists_hom_of_thick J τ fun e χ => by`. Take `⟨σ, -, h₁, h₂⟩` from `t.tor e`. Use `(t.l (e + 1)).Q.mono_i_left` as an intermediate fact. Use `mF (e + 1)` as an intermediate fact. Establish `h₃ : thickMap V I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left` using `(pullback.lift_fst _ _ _).trans (Category.comp_id _)`.

Establish `h₄ : thickTrans W J e ≫ y (e + 1) = y e ≫ thickMap V I e G`. Use `(cancel_mono (fstG I (e + 1) G).left).1 ?_` and prove the remaining obligations. Use `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hy (e + 1))).trans ?_)` and prove the remaining obligations. Use `Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₃)).symm` and prove the remaining obligations. Rewrite using `[← Category.assoc, thickTrans_comp]`.

Conclude with `(hy e).symm`. Establish `h₅ : thickTrans W J e ≫ τ (e + 1) = τ e ≫ σ`. Rewrite using `[← cancel_mono (t.l (e + 1)).Q.i.left, Category.assoc, hτ, h₄, Category.assoc, h₂, ← Category.assoc, hτ]`. Rewrite using `[h₅, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, h₁]`. Use `⟨c, fun e Z r τ' h₁ h₂ => ?_⟩` and prove the remaining obligations.

Take `⟨r', rfl⟩` from `exists_factor_thick φ I e r _ ((Category.assoc _ _ _).trans h₁)`. Establish `h₃ : τ' = r' ≫ τ e`. Use `splitTorus_left_hom_ext _ _ ?_ fun χ => ?_` and prove the remaining obligations. Rewrite using `[← cancel_mono (thick V I e), Category.assoc]`. Use `h₁.trans ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, base e _ _ (hy e), ← hτ e, Category.assoc (τ e), Over.w]`. Simplify using `only [Category.assoc]`. Rewrite using `[h₂, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hc, scal, scal, Scheme.Hom.comp_appTop]`. Both sides reduce to the same expression. Establish `h₄ : τ e ≫ (t.l e).Q.i.left ≫ (fstG I e G).left = thick W J e ≫ x.left` using `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I e G).left) (hτ e)).trans (hy e))`.

Rewrite using `[h₃]`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (r' ≫ ·) h₄).trans (Category.assoc _ _ _).symm)`. Introduce and unpack `⟨c, hc⟩ e Z r xe h`. Take `⟨τ, h₁, h₂⟩` from `exists_torus_point c r (xe ≫ (thickObj V I e G).hom)`. Use `mF e` as an intermediate fact.

Use `(ker e r xe h).2 ⟨τ, (cancel_mono (fstG I e G).left).1 ?_⟩` and prove the remaining obligations. Use `(Category.assoc _ _ _).trans ((hc e Z r τ ?_ h₂).trans h.symm)` and prove the remaining obligations. Rewrite using `[← Category.assoc, h₁]`. Conclude with `(base e r xe h).symm`.
-/
theorem image_eq_one_iff_torus_point : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ↔ ∃ c : Multiplicative s.X →* Wˣ, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ (Spec.map (CommRingCat.ofHom (algebraMap V W))) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (c (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ (x).left) := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ x
  let I := IsLocalRing.maximalIdeal V
  let φ := algebraMap V W
  have hx : x.left ≫ G.hom = Spec.map (CommRingCat.ofHom φ) := Over.w x
  have hF : ∀ e, (fstG I e G).left ≫ G.hom = (thickObj V I e G).hom ≫ thick V I e := fun e => pullback.condition
  have mF : ∀ e, Mono (fstG I e G).left := fun e => pullback.fst_of_mono (f := G.hom) (g := thick V I e)
  have base : ∀ (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x.left →
      r ≫ Spec.map (CommRingCat.ofHom φ) = (xe ≫ (thickObj V I e G).hom) ≫ thick V I e := fun e Z r xe h => by
    rw [Category.assoc, ← hF, ← hx, ← Category.assoc, ← h]
    exact Category.assoc _ _ _
  have ker := fun (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V I e G).left)
    (h : xe ≫ (fstG I e G).left = r ≫ x.left) =>
    (t.l e).Q.image_eq_one_iff (T := Over.mk (Spec.map (CommRingCat.ofHom φ))) (a.b_pb e).1 r xe (base e r xe h)
  constructor
  · intro H
    let J := I.map φ
    have hle : ∀ e : ℕ, I ^ (e + 1) ≤ (J ^ (e + 1)).comap φ := fun e => by
      rw [← Ideal.map_pow]; exact Ideal.le_comap_map
    have hp : ∀ e, (thick W J e ≫ x.left) ≫ G.hom =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ (hle e))) ≫ thick V I e := fun e => by
      rw [Category.assoc, hx, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
    obtain ⟨y, hy⟩ : ∃ y : ∀ e, Spec (CommRingCat.of (W ⧸ J ^ (e + 1))) ⟶ (thickObj V I e G).left,
        ∀ e, y e ≫ (fstG I e G).left = thick W J e ≫ x.left :=
      ⟨fun e => pullback.lift _ _ (hp e), fun e => pullback.lift_fst _ _ _⟩
    choose τ hτ using fun e => (ker e _ _ (hy e)).1 (H e _ _ _ (hy e))
    obtain ⟨c, hc⟩ := exists_hom_of_thick J τ fun e χ => by
      obtain ⟨σ, -, h₁, h₂⟩ := t.tor e
      have := (t.l (e + 1)).Q.mono_i_left
      have := mF (e + 1)
      have h₃ : thickMap V I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
        (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      have h₄ : thickTrans W J e ≫ y (e + 1) = y e ≫ thickMap V I e G := by
        refine (cancel_mono (fstG I (e + 1) G).left).1 ?_
        refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hy (e + 1))).trans ?_)
        refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₃)).symm
        rw [← Category.assoc, thickTrans_comp]
        exact (hy e).symm
      have h₅ : thickTrans W J e ≫ τ (e + 1) = τ e ≫ σ := by
        rw [← cancel_mono (t.l (e + 1)).Q.i.left, Category.assoc, hτ, h₄, Category.assoc, h₂, ← Category.assoc, hτ]
      rw [h₅, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, h₁]
    refine ⟨c, fun e Z r τ' h₁ h₂ => ?_⟩
    obtain ⟨r', rfl⟩ := exists_factor_thick φ I e r _ ((Category.assoc _ _ _).trans h₁)
    have h₃ : τ' = r' ≫ τ e := by
      refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
      · rw [← cancel_mono (thick V I e), Category.assoc]
        refine h₁.trans ?_
        rw [Category.assoc, base e _ _ (hy e), ← hτ e, Category.assoc (τ e), Over.w]
        simp only [Category.assoc]
      · rw [h₂, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hc, scal, scal,
          Scheme.Hom.comp_appTop]
        rfl
    have h₄ : τ e ≫ (t.l e).Q.i.left ≫ (fstG I e G).left = thick W J e ≫ x.left :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I e G).left) (hτ e)).trans (hy e))
    rw [h₃]
    exact (Category.assoc _ _ _).trans ((congrArg (r' ≫ ·) h₄).trans (Category.assoc _ _ _).symm)
  · rintro ⟨c, hc⟩ e Z r xe h
    obtain ⟨τ, h₁, h₂⟩ := exists_torus_point c r (xe ≫ (thickObj V I e G).hom)
    have := mF e
    refine (ker e r xe h).2 ⟨τ, (cancel_mono (fstG I e G).left).1 ?_⟩
    refine (Category.assoc _ _ _).trans ((hc e Z r τ ?_ h₂).trans h.symm)
    rw [← Category.assoc, h₁]
    exact (base e r xe h).symm

end GlobalTheory.UU
