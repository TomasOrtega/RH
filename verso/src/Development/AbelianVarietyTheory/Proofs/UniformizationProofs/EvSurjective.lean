import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsNilpotentOfRd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.CubeLift

open SplitTorus (ev univPt ptOf pull bcMap ofVal valHom)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (chi torusFst)

section Expand

variable {S S' : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {R : CommRingCat.{0}}

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem app_global_comp_apply {U V W' : Scheme.{0}} (f : U ⟶ V) (g : V ⟶ W') (u : Γ(W', ⊤)) :
    (f ≫ g).appTop.hom u = f.appTop.hom (g.appTop.hom u) := by
  rfl

/- English proof (translation)
Simplify using `only [SplitTorus.pull, RingHom.comp_apply, Over.comp_left, app_global_comp_apply]`.
-/
private theorem splitTorus_pull_comp {B : CommRingCat.{0}} {s : Spec B ⟶ S}
    (g : Over.mk s ⟶ splitTorus S Y) (h : splitTorus S Y ⟶ splitTorus S X) (u : Γ((splitTorus S X).left, ⊤)) :
    pull (g ≫ h) u = pull g (h.left.appTop.hom u) := by
  simp only [SplitTorus.pull, RingHom.comp_apply, Over.comp_left, app_global_comp_apply]

/- English proof (translation)
Establish `key : ∀ hs, univPt Y t ≫ SplitTorus.torusMap S φ = ptOf (B` using `CommRingCat.of (AddMonoidAlgebra R Y)) t (mv φ) hs := by`. Introduce `hs`. Use `SplitTorus.pull_ext fun a => ?_` and prove the remaining obligations. Rewrite using `[SplitTorus.pull_ptOf, splitTorus_pull_comp, SplitTorus.torusMap_appTop_chi]`. Express the relevant statement in the definitionally equal form `ev t _ = _`.

Rewrite using `[SplitTorus.ev_chi, SplitTorus.ev_chi, mv_single]`. Establish `hs : Spec.map (CommRingCat.ofHom ((mv φ : AddMonoidAlgebra R X →+* AddMonoidAlgebra R Y).comp (algebraMap R (AddMonoidAlgebra R X)))) ≫ t = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R Y))) ≫ t`. Use `congr 3`. Use extensionality with `r`. Simplify using `[mv]`.

Express the relevant statement in the definitionally equal form `pull (univPt Y t) _ = _`. Rewrite using `[← splitTorus_pull_comp, key hs, SplitTorus.pull_ptOf]`.
-/
theorem ev_torusMap (t : Spec R ⟶ S) (φ : X →+ Y) (u : Γ((splitTorus S X).left, ⊤)) :
    ev t ((SplitTorus.torusMap S φ).left.appTop.hom u) = mv φ (ev t u) := by
  have key : ∀ hs, univPt Y t ≫ SplitTorus.torusMap S φ =
      ptOf (B := CommRingCat.of (AddMonoidAlgebra R Y)) t (mv φ) hs := by
    intro hs
    refine SplitTorus.pull_ext fun a => ?_
    rw [SplitTorus.pull_ptOf, splitTorus_pull_comp, SplitTorus.torusMap_appTop_chi]
    change ev t _ = _
    rw [SplitTorus.ev_chi, SplitTorus.ev_chi, mv_single]
  have hs : Spec.map (CommRingCat.ofHom ((mv φ : AddMonoidAlgebra R X →+* AddMonoidAlgebra R Y).comp
      (algebraMap R (AddMonoidAlgebra R X)))) ≫ t =
      Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R Y))) ≫ t := by
    congr 3
    ext r
    simp [mv]
  change pull (univPt Y t) _ = _
  rw [← splitTorus_pull_comp, key hs, SplitTorus.pull_ptOf]

/- English proof (translation)
Establish `e : (univPt X t).left ≫ bcMap f X = (univPt X (t ≫ f)).left`. Use `splitTorus_left_hom_ext _ _ ?_ fun χ => ?_` and prove the remaining obligations. Simplify using `[SplitTorus.bcMap_hom]`. Establish `h0 : (Scheme.ΓSpecIso _).hom.hom (SplitTorus.val (univPt X t) χ) = (Scheme.ΓSpecIso _).hom.hom (SplitTorus.val (univPt X (t ≫ f)) χ)`. Rewrite using `[← SplitTorus.pull_chi, ← SplitTorus.pull_chi]`.

Conclude with `(SplitTorus.ev_chi t χ).trans (SplitTorus.ev_chi (t ≫ f) χ).symm`. Establish `h1` using `congrArg (Scheme.ΓSpecIso _).inv.hom h0`. Simplify using `only [Iso.hom_inv_id_apply] at h1`. Rewrite `h1` using `[SplitTorus.val_eq, SplitTorus.val_eq]`. Rewrite using `[app_global_comp_apply, SplitTorus.charUnit_val, SplitTorus.bcMap_appTop_chi]`.

Conclude with `h1`. Express the relevant statement in the definitionally equal form `pull (univPt X t) _ = pull (univPt X (t ≫ f)) u`. Simplify using `only [SplitTorus.pull, RingHom.comp_apply, ← e, app_global_comp_apply]`.
-/
theorem ev_bcMap (f : S' ⟶ S) (t : Spec R ⟶ S') (u : Γ((splitTorus S X).left, ⊤)) :
    ev t ((bcMap f X).appTop.hom u) = ev (t ≫ f) u := by
  have e : (univPt X t).left ≫ bcMap f X = (univPt X (t ≫ f)).left := by
    refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · simp [SplitTorus.bcMap_hom]
    · have h0 : (Scheme.ΓSpecIso _).hom.hom (SplitTorus.val (univPt X t) χ) =
          (Scheme.ΓSpecIso _).hom.hom (SplitTorus.val (univPt X (t ≫ f)) χ) := by
        rw [← SplitTorus.pull_chi, ← SplitTorus.pull_chi]
        exact (SplitTorus.ev_chi t χ).trans (SplitTorus.ev_chi (t ≫ f) χ).symm
      have h1 := congrArg (Scheme.ΓSpecIso _).inv.hom h0
      simp only [Iso.hom_inv_id_apply] at h1
      rw [SplitTorus.val_eq, SplitTorus.val_eq] at h1
      rw [app_global_comp_apply, SplitTorus.charUnit_val, SplitTorus.bcMap_appTop_chi]
      exact h1
  change pull (univPt X t) _ = pull (univPt X (t ≫ f)) u
  simp only [SplitTorus.pull, RingHom.comp_apply, ← e, app_global_comp_apply]

/- English proof (translation)
Introduce `u v h`. Use `SplitTorus.eq_of_ev fun B t => ?_` and prove the remaining obligations. Take `⟨φ, rfl⟩ : ∃ φ, Spec.map φ ≫ 𝟙 _ = t` from `⟨Spec.preimage t, by simp⟩`. Rewrite using `[SplitTorus.ev_comp, SplitTorus.ev_comp, h]`.
-/
theorem ev_injective : Function.Injective (ev (X := X) (𝟙 (Spec R))) := by
  intro u v h
  refine SplitTorus.eq_of_ev fun B t => ?_
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ ≫ 𝟙 _ = t := ⟨Spec.preimage t, by simp⟩
  rw [SplitTorus.ev_comp, SplitTorus.ev_comp, h]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `pull (univPt X _) _ = _`. Establish `hw` using `Over.w (univPt X (𝟙 (Spec R)))`. Simplify using `only [SplitTorus.pull, RingHom.comp_apply]`. Rewrite using `[← app_global_comp_apply, hw]`. Use `erw [Category.comp_id]`.

Use `erw [SplitTorus.specMap_appTop_apply, Iso.inv_hom_id_apply]`. Both sides reduce to the same expression.
-/
private theorem ev_base_apply (r : R) :
    ev (X := X) (𝟙 (Spec R)) ((splitTorus (Spec R) X).hom.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)) =
      AddMonoidAlgebra.single 0 r := by
  change pull (univPt X _) _ = _
  have hw := Over.w (univPt X (𝟙 (Spec R)))
  simp only [SplitTorus.pull, RingHom.comp_apply]
  rw [← app_global_comp_apply, hw]
  erw [Category.comp_id]
  erw [SplitTorus.specMap_appTop_apply, Iso.inv_hom_id_apply]
  rfl

/- English proof (translation)
Introduce `w`. Proceed by induction on `w using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `add p q hp hq`. Take `⟨a, rfl⟩` from `hp`.

Take `⟨b, rfl⟩` from `hq`. Conclude with `⟨a + b, map_add _ _ _⟩`. Consider the case `single x r`. Use `⟨(splitTorus (Spec R) X).hom.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) * chi X x, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, SplitTorus.ev_chi, ev_base_apply, AddMonoidAlgebra.single_mul_single, zero_add, _root_.mul_one]`.
-/
theorem ev_surjective : Function.Surjective (ev (X := X) (𝟙 (Spec R))) := by
  intro w
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    refine ⟨(splitTorus (Spec R) X).hom.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) * chi X x, ?_⟩
    rw [map_mul, SplitTorus.ev_chi, ev_base_apply, AddMonoidAlgebra.single_mul_single, zero_add, _root_.mul_one]

end Expand

section Points

variable {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {Z Z' V : Over S}

abbrev app {Z V : Scheme.{0}} (r : Z ⟶ V) : Γ(V, ⊤)ˣ →* Γ(Z, ⊤)ˣ := Units.map r.appTop.hom.toMonoidHom

/- English proof (translation)
Use `ext`. Conclude with `(app_global_comp_apply r s u.val).symm`.
-/
theorem app_app {Z Z' V : Scheme.{0}} (r : Z' ⟶ Z) (s : Z ⟶ V) (u : Γ(V, ⊤)ˣ) : app r (app s u) = app (r ≫ s) u := by
  ext
  exact (app_global_comp_apply r s u.val).symm

def pt (x y u : Z ⟶ splitTorus S X) : Z ⟶ splitTorus S (X × X × X) :=
  ofVal ((valHom x).coprod ((valHom y).coprod (valHom u)))

/- English proof (translation)
Use `SplitTorus.hom_ext fun a => ?_` and prove the remaining obligations. Rewrite using `[SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]`. Simplify using the standard rewrite rules.
-/
theorem pt_p₁ (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₁ = x := by
  refine SplitTorus.hom_ext fun a => ?_
  rw [SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]
  simp

/- English proof (translation)
Use `SplitTorus.hom_ext fun a => ?_` and prove the remaining obligations. Rewrite using `[SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]`. Simplify using the standard rewrite rules.
-/
theorem pt_p₂ (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₂ = y := by
  refine SplitTorus.hom_ext fun a => ?_
  rw [SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]
  simp

/- English proof (translation)
Use `SplitTorus.hom_ext fun a => ?_` and prove the remaining obligations. Rewrite using `[SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]`. Simplify using the standard rewrite rules.
-/
theorem pt_p₃ (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₃ = u := by
  refine SplitTorus.hom_ext fun a => ?_
  rw [SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]
  simp

/- English proof (translation)
Use `SplitTorus.hom_ext fun p => ?_` and prove the remaining obligations. Take `⟨x, y, z⟩` from `p`. Rewrite using `[pt, SplitTorus.val_ofVal, SplitTorus.val_torusMap]`. Simplify using `only [AddMonoidHom.coprod_apply, toMul_add, Units.val_mul, SplitTorus.valHom_apply, SplitTorus.val_torusMap, tri]`. Rewrite using `[← SplitTorus.val_id, ← SplitTorus.val_id, ← SplitTorus.val_id, ← SplitTorus.val_id, SplitTorus.val_add, SplitTorus.val_add]`.
-/
theorem pt_torusMap (a b c : X →+ Y) : pt (SplitTorus.torusMap S a) (SplitTorus.torusMap S b) (SplitTorus.torusMap S c) = SplitTorus.torusMap S (tri a b c) := by
  refine SplitTorus.hom_ext fun p => ?_
  obtain ⟨x, y, z⟩ := p
  rw [pt, SplitTorus.val_ofVal, SplitTorus.val_torusMap]
  simp only [AddMonoidHom.coprod_apply, toMul_add, Units.val_mul, SplitTorus.valHom_apply,
    SplitTorus.val_torusMap, tri]
  rw [← SplitTorus.val_id, ← SplitTorus.val_id, ← SplitTorus.val_id, ← SplitTorus.val_id,
    SplitTorus.val_add, SplitTorus.val_add]

def dif [GrpObj V] (g : Γ(V.left, ⊤)ˣ) (x y u : Z ⟶ V) : Γ(Z.left, ⊤)ˣ :=
  app (x * y * u).left g * app x.left g * app y.left g * app u.left g / app (x * y).left g / app (x * u).left g /
    app (y * u).left g

/- English proof (translation)
Simplify using `only [dif, map_mul, map_div, app_app, ← Over.comp_left, Hom.mul_def, comp_lift_assoc]`.
-/
theorem app_dif [GrpObj V] (g : Γ(V.left, ⊤)ˣ) (r : Z' ⟶ Z) (x y u : Z ⟶ V) :
    app r.left (dif g x y u) = dif g (r ≫ x) (r ≫ y) (r ≫ u) := by
  simp only [dif, map_mul, map_div, app_app, ← Over.comp_left, Hom.mul_def, comp_lift_assoc]

end Points

section Affine

variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

abbrev ex : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ →* (AddMonoidAlgebra A X)ˣ :=
  Units.map (ev (X := X) (𝟙 (Spec (CommRingCat.of A)))).toMonoidHom

/- English proof (translation)
Establish `hi` using `ev_injective (R := CommRingCat.of A) (X := X)`. Establish `hs` using `ev_surjective (R := CommRingCat.of A) (X := X)`. Use `⟨fun u v h => Units.ext (hi (congrArg Units.val h)), fun w => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hs w.val`. Take `⟨b, hb⟩` from `hs w.inv`.

Establish `hab : a * b = 1` using `hi (by rw [map_mul, ha, hb, w.val_inv, map_one])`. Conclude with `⟨⟨a, b, hab, by rw [_root_.mul_comm, hab]⟩, Units.ext ha⟩`.
-/
theorem ex_bijective : Function.Bijective (ex (A := A) (X := X)) := by
  have hi := ev_injective (R := CommRingCat.of A) (X := X)
  have hs := ev_surjective (R := CommRingCat.of A) (X := X)
  refine ⟨fun u v h => Units.ext (hi (congrArg Units.val h)), fun w => ?_⟩
  obtain ⟨a, ha⟩ := hs w.val
  obtain ⟨b, hb⟩ := hs w.inv
  have hab : a * b = 1 := hi (by rw [map_mul, ha, hb, w.val_inv, map_one])
  exact ⟨⟨a, b, hab, by rw [_root_.mul_comm, hab]⟩, Units.ext ha⟩

/- English proof (translation)
The claim follows from `Units.ext (ev_torusMap (𝟙 _) φ u.val)`.
-/
theorem ex_app (φ : X →+ Y) (u : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ) :
    ex (app (SplitTorus.torusMap _ φ).left u) = um φ (ex u) := Units.ext (ev_torusMap (𝟙 _) φ u.val)

/- English proof (translation)
Simplify using `only [dif, del, map_mul, map_div, ← SplitTorus.torusMap_add, ex_app]`.
-/
theorem ex_dif (a b c : X →+ Y) (g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ) :
    ex (dif g (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b) (SplitTorus.torusMap _ c)) = del (ex g) a b c := by
  simp only [dif, del, map_mul, map_div, ← SplitTorus.torusMap_add, ex_app]

/- English proof (translation)
Establish `key : ev (𝟙 _) ((bcMap (red J) X).appTop.hom u.val) = rd J (ev (𝟙 _) u.val)`. Rewrite using `[ev_bcMap, Category.id_comp, show red J = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ 𝟙 _ from (Category.comp_id _).symm, SplitTorus.ev_comp]`. Both sides reduce to the same expression. Rewrite using `[mem_cong, Units.ext_iff, Units.val_one]`. Express the relevant statement in the definitionally equal form `rd J (ev (𝟙 _) u.val) = 1 ↔ (bcMap (red J) X).appTop.hom u.val = 1`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `ev_injective` to reduce the goal to its premises. Rewrite using `[key, h, map_one]`. Introduce `h`.

Rewrite using `[← key, h, map_one]`.
-/
theorem ex_mem_cong (J : Ideal A) (u : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ) :
    ex u ∈ cong J ↔ app (bcMap (red J) X) u = 1 := by
  have key : ev (𝟙 _) ((bcMap (red J) X).appTop.hom u.val) = rd J (ev (𝟙 _) u.val) := by
    rw [ev_bcMap, Category.id_comp,
      show red J = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ 𝟙 _ from (Category.comp_id _).symm,
      SplitTorus.ev_comp]
    rfl
  rw [mem_cong, Units.ext_iff, Units.val_one]
  change rd J (ev (𝟙 _) u.val) = 1 ↔ (bcMap (red J) X).appTop.hom u.val = 1
  constructor
  · intro h
    apply ev_injective
    rw [key, h, map_one]
  · intro h
    rw [← key, h, map_one]

variable {J : Ideal A}

/- English proof (translation)
Establish `hcub : Cub (ex (A` using `A) (X := X × X × X) D) := by`. Use `⟨fun Y _ a b c => ?_, fun Y _ a b c => ?_, fun Y _ a b c d => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg ex (s₁ (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b) (SplitTorus.torusMap _ c))`. Simplify `h1` using `only [pt_torusMap, ex_app]`. Establish `h1` using `congrArg ex (s₂ (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b) (SplitTorus.torusMap _ c))`.

Simplify `h1` using `only [pt_torusMap, ex_app]`. Establish `h1` using `congrArg ex (co (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b) (SplitTorus.torusMap _ c) (SplitTorus.torusMap _ d))`. Simplify `h1` using `only [← SplitTorus.torusMap_add, pt_torusMap, map_mul, ex_app]`. Take `⟨g', hg', hD⟩` from `hcub.exists_del hJ ((ex_mem_cong J D).2 h)`. Take `⟨g, rfl⟩` from `(ex_bijective (A := A) (X := X)).2 g'`.

Establish `hD' : D = dif g (SplitTorus.torusMap _ p₁) (SplitTorus.torusMap _ p₂) (SplitTorus.torusMap _ p₃)`. Apply `(ex_bijective (A := A) (X := X × X × X)).1` to reduce the goal to its premises. Rewrite using `[hD, ex_dif]`. Use `⟨g, (ex_mem_cong J g).1 hg', fun Z x y u => ?_⟩` and prove the remaining obligations. Rewrite using `[hD', app_dif, pt_p₁, pt_p₂, pt_p₃]`.
-/
theorem exists_dif (hJ : IsNilpotent J) (D : Γ((splitTorus (Spec (CommRingCat.of A)) (X × X × X)).left, ⊤)ˣ)
    (s₁ : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X),
      app (pt x y u).left D = app (pt y x u).left D)
    (s₂ : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X),
      app (pt x y u).left D = app (pt x u y).left D)
    (co : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u v : Z ⟶ splitTorus _ X),
      app (pt (x * y) u v).left D * app (pt x y v).left D = app (pt x (y * u) v).left D * app (pt y u v).left D)
    (h : app (bcMap (red J) _) D = 1) :
    ∃ g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ, app (bcMap (red J) X) g = 1 ∧
      ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X), app (pt x y u).left D = dif g x y u := by
  have hcub : Cub (ex (A := A) (X := X × X × X) D) := by
    refine ⟨fun Y _ a b c => ?_, fun Y _ a b c => ?_, fun Y _ a b c d => ?_⟩
    · have h1 := congrArg ex (s₁ (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b)
        (SplitTorus.torusMap _ c))
      simpa only [pt_torusMap, ex_app] using h1
    · have h1 := congrArg ex (s₂ (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b)
        (SplitTorus.torusMap _ c))
      simpa only [pt_torusMap, ex_app] using h1
    · have h1 := congrArg ex (co (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b)
        (SplitTorus.torusMap _ c) (SplitTorus.torusMap _ d))
      simpa only [← SplitTorus.torusMap_add, pt_torusMap, map_mul, ex_app] using h1
  obtain ⟨g', hg', hD⟩ := hcub.exists_del hJ ((ex_mem_cong J D).2 h)
  obtain ⟨g, rfl⟩ := (ex_bijective (A := A) (X := X)).2 g'
  have hD' : D = dif g (SplitTorus.torusMap _ p₁) (SplitTorus.torusMap _ p₂) (SplitTorus.torusMap _ p₃) := by
    apply (ex_bijective (A := A) (X := X × X × X)).1
    rw [hD, ex_dif]
  refine ⟨g, (ex_mem_cong J g).1 hg', fun Z x y u => ?_⟩
  rw [hD', app_dif, pt_p₁, pt_p₂, pt_p₃]

/- English proof (translation)
Establish `h1 : ex g ∈ cong J` using `(ex_mem_cong J g).2 h`. Establish `h2 : del (ex g) p₁ p₂ p₃ = 1`. Rewrite using `[← ex_dif, hg, map_one]`. Apply `(ex_bijective (A := A) (X := X)).1` to reduce the goal to its premises. Rewrite using `[eq_one_of_del hJ h1 h2, map_one]`.
-/
theorem eq_one_of_dif (hJ : IsNilpotent J) (g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ)
    (h : app (bcMap (red J) X) g = 1)
    (hg : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X), dif g x y u = 1) : g = 1 := by
  have h1 : ex g ∈ cong J := (ex_mem_cong J g).2 h
  have h2 : del (ex g) p₁ p₂ p₃ = 1 := by
    rw [← ex_dif, hg, map_one]
  apply (ex_bijective (A := A) (X := X)).1
  rw [eq_one_of_del hJ h1 h2, map_one]

end Affine

end GlobalTheory.CubeLift
