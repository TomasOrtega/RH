import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinitePresentationOfInjective

universe u

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

namespace GlobalTheory.Diag

variable (S : Scheme.{u}) {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]

omit [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] in

/- English proof (translation)
Establish `hs : ∀ s : PullbackCone f e, s.fst ≫ f = toUnit _ ≫ e` using `fun s => by`. Rewrite using `[s.condition, toUnit_unique s.snd (toUnit _)]`. Conclude with `⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (hl s.fst (hs s)).choose) (fun s => (hl s.fst (hs s)).choose_spec) (fun s => toUnit_unique _ _) (fun s m h _ => hmono (h.trans (hl s.fst (hs s)).choose_spec.symm))⟩⟩`.
-/
theorem isPullback_toUnit_of_lift {K G H : Over S} {i : K ⟶ G} {f : G ⟶ H} {e : 𝟙_ (Over S) ⟶ H}
    (hw : i ≫ f = toUnit _ ≫ e)
    (hmono : ∀ {T : Over S} {a b : T ⟶ K}, a ≫ i = b ≫ i → a = b)
    (hl : ∀ {T : Over S} (t : T ⟶ G), t ≫ f = toUnit _ ≫ e → ∃ l : T ⟶ K, l ≫ i = t) :
    IsPullback i (toUnit _) f e := by
  have hs : ∀ s : PullbackCone f e, s.fst ≫ f = toUnit _ ≫ e := fun s => by
    rw [s.condition, toUnit_unique s.snd (toUnit _)]
  exact ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (hl s.fst (hs s)).choose)
    (fun s => (hl s.fst (hs s)).choose_spec) (fun s => toUnit_unique _ _)
    (fun s m h _ => hmono (h.trans (hl s.fst (hs s)).choose_spec.symm))⟩⟩

def ringMap (u : Y →+ X) : torusRing ZU Y ⟶ torusRing ZU X :=
  CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom ZU.{u} u)

/- English proof (translation)
The claim follows from `AddMonoidAlgebra.mapDomain_single`.
-/
theorem ringMap_single (u : Y →+ X) (y : Y) (r : ZU.{u}) :
    (ringMap u).hom (AddMonoidAlgebra.single y r) = AddMonoidAlgebra.single (u y) r :=
  AddMonoidAlgebra.mapDomain_single

def affMap (u : Y →+ X) : splitTorusAff ZU X ⟶ splitTorusAff ZU Y :=
  Spec.mapMulEquiv (R := ZU.{u}) (S := AddMonoidAlgebra ZU.{u} Y) (T := AddMonoidAlgebra ZU.{u} X)
    (WithConv.toConv (AddMonoidAlgebra.mapDomainAlgHom ZU.{u} ZU.{u} u))

instance (u : Y →+ X) : IsMonHom (affMap u) :=
  ((bialgSpec ZU.{u}).map (CommBialgCat.ofHom
    (AddMonoidAlgebra.mapDomainBialgHom ZU.{u} u)).op).isMonHom_hom

/- English proof (translation)
Rewrite using `[affMap, affMap, affMap]`. Use `Eq.trans (congrArg _ ?_) (map_mul (Spec.mapMulEquiv (R := ZU.{u}) (S := AddMonoidAlgebra ZU.{u} Y) (T := AddMonoidAlgebra ZU.{u} X)) _ _)` and prove the remaining obligations. Use extensionality with `y : 2`. Rewrite using `[AddMonoidAlgebra.convMul_algHom_single_one]`. Simplify using `[AddMonoidAlgebra.single_mul_single]`.

Conclude with `Subsingleton.elim _ _`.
-/
theorem affMap_add (u v : Y →+ X) : affMap (u + v) = affMap u * affMap v := by
  rw [affMap, affMap, affMap]
  refine Eq.trans (congrArg _ ?_) (map_mul (Spec.mapMulEquiv (R := ZU.{u})
    (S := AddMonoidAlgebra ZU.{u} Y) (T := AddMonoidAlgebra ZU.{u} X)) _ _)
  ext y : 2
  · rw [AddMonoidAlgebra.convMul_algHom_single_one]
    simp [AddMonoidAlgebra.single_mul_single]
  · exact Subsingleton.elim _ _

def diagMap (u : Y →+ X) : splitTorus S X ⟶ splitTorus S Y :=
  (Over.pullback (toZ S)).map (affMap u)

instance diagMap_isMonHom (u : Y →+ X) : IsMonHom (diagMap S u) :=
  Functor.map.instIsMonHom (F := Over.pullback (toZ S)) (f := affMap u)

instance isCommMonObj (X : Type u) [AddCommGroup X] : IsCommMonObj (splitTorus S X) :=
  inferInstanceAs (IsCommMonObj ((Over.pullback (toZ S)).obj (splitTorusAff ZU X)))

/- English proof (translation)
Rewrite using `[diagMap, affMap_add]`. Conclude with `Functor.map_mul (Over.pullback (toZ S)) _ _`.
-/
theorem diagMap_add (u v : Y →+ X) : diagMap S (u + v) = diagMap S u * diagMap S v := by
  rw [diagMap, affMap_add]
  exact Functor.map_mul (Over.pullback (toZ S)) _ _

/- English proof (translation)
Establish `h` using `diagMap_add S (0 : Y →+ X) 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_eq_left.1 h.symm`.
-/
theorem diagMap_zero : diagMap S (0 : Y →+ X) = 1 := by
  have h := diagMap_add S (0 : Y →+ X) 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
theorem diagMap_left_torusFst (u : Y →+ X) :
    (diagMap S u).left ≫ torusFst S Y = torusFst S X ≫ Spec.map (ringMap u) :=
  pullback.lift_fst _ _ _

/- English proof (translation)
The claim follows from `IsPullback.of_hasPullback _ _`.
-/
theorem isPullback_torusFst (X : Type u) [AddCommGroup X] :
    IsPullback (torusFst S X) (splitTorus S X).hom (splitTorusAff ZU X).hom (toZ S) :=
  IsPullback.of_hasPullback _ _

/- English proof (translation)
Use `IsPullback.of_bot ?_ (diagMap_left_torusFst S u).symm (isPullback_torusFst S Y)` and prove the remaining obligations. Establish `e : Spec.map (ringMap u) ≫ (splitTorusAff ZU Y).hom = (splitTorusAff ZU X).hom` using `specULiftZIsTerminal.hom_ext _ _`. Rewrite using `[Over.w, e]`. Conclude with `isPullback_torusFst S X`.
-/
theorem isPullback_diagMap (u : Y →+ X) :
    IsPullback (torusFst S X) (diagMap S u).left (Spec.map (ringMap u)) (torusFst S Y) := by
  refine IsPullback.of_bot ?_ (diagMap_left_torusFst S u).symm (isPullback_torusFst S Y)
  have e : Spec.map (ringMap u) ≫ (splitTorusAff ZU Y).hom = (splitTorusAff ZU X).hom :=
    specULiftZIsTerminal.hom_ext _ _
  rw [Over.w, e]
  exact isPullback_torusFst S X

variable {S} in
/- English proof (translation)
Simplify using `only [coord, Over.comp_left, Category.assoc, diagMap_left_torusFst, Scheme.Hom.comp_appTop]`. Rewrite using `[← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]`.
-/
theorem coord_comp_diagMap {T : Over S} (t : T ⟶ splitTorus S X) (u : Y →+ X) :
    coord (t ≫ diagMap S u) = ringMap u ≫ coord t := by
  simp only [coord, Over.comp_left, Category.assoc, diagMap_left_torusFst, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

variable {S} in
/- English proof (translation)
Rewrite using `[coord_comp_diagMap, CommRingCat.hom_comp, RingHom.comp_apply, ringMap_single]`.
-/
theorem coord_comp_diagMap_single {T : Over S} (t : T ⟶ splitTorus S X) (u : Y →+ X) (y : Y) :
    (coord (t ≫ diagMap S u)).hom (AddMonoidAlgebra.single y 1) =
      (coord t).hom (AddMonoidAlgebra.single (u y) 1) := by
  rw [coord_comp_diagMap, CommRingCat.hom_comp, RingHom.comp_apply, ringMap_single]

/- English proof (translation)
Rewrite using `[chi, chi, ← coord_comp_diagMap_single, Category.id_comp, ← Category.comp_id (diagMap S u), coord_comp, Category.comp_id]`. Both sides reduce to the same expression.
-/
theorem diagMap_chi (u : Y →+ X) (y : Y) : (diagMap S u).left.appTop.hom (chi Y y) = chi X (u y) := by
  rw [chi, chi, ← coord_comp_diagMap_single, Category.id_comp, ← Category.comp_id (diagMap S u), coord_comp,
    Category.comp_id]
  rfl

variable {S} in

/- English proof (translation)
The claim follows from `coord_injective (CommRingCat.hom_ext (ringHom_ext_ZU h))`.
-/
theorem hom_ext {T : Over S} {s t : T ⟶ splitTorus S X}
    (h : ∀ x, (coord s).hom (AddMonoidAlgebra.single x 1) =
      (coord t).hom (AddMonoidAlgebra.single x 1)) : s = t :=
  coord_injective (CommRingCat.hom_ext (ringHom_ext_ZU h))

/- English proof (translation)
The claim follows from `hom_ext fun x => by rw [← Category.id_comp (diagMap S _), coord_comp_diagMap_single]; rfl`.
-/
theorem diagMap_id : diagMap S (AddMonoidHom.id X) = 𝟙 _ :=
  hom_ext fun x => by rw [← Category.id_comp (diagMap S _), coord_comp_diagMap_single]; rfl

/- English proof (translation)
The claim follows from `hom_ext fun x => by rw [coord_comp_diagMap_single, ← Category.id_comp (diagMap S u), coord_comp_diagMap_single, ← Category.id_comp (diagMap S (u.comp v)), coord_comp_diagMap_single]; rfl`.
-/
theorem diagMap_comp (u : Y →+ X) (v : Z →+ Y) : diagMap S (u.comp v) = diagMap S u ≫ diagMap S v :=
  hom_ext fun x => by
    rw [coord_comp_diagMap_single, ← Category.id_comp (diagMap S u), coord_comp_diagMap_single,
      ← Category.id_comp (diagMap S (u.comp v)), coord_comp_diagMap_single]; rfl

variable {S} in

/- English proof (translation)
Rewrite using `[← MonObj.comp_one (1 : T ⟶ splitTorus S X), ← diagMap_zero, coord_comp_diagMap_single, AddMonoidHom.zero_apply, ← AddMonoidAlgebra.one_def, map_one]`.
-/
theorem coord_one (T : Over S) (x : X) :
    (coord (1 : T ⟶ splitTorus S X)).hom (AddMonoidAlgebra.single x 1) = 1 := by
  rw [← MonObj.comp_one (1 : T ⟶ splitTorus S X), ← diagMap_zero, coord_comp_diagMap_single,
    AddMonoidHom.zero_apply, ← AddMonoidAlgebra.one_def, map_one]

variable {S} in

def ofCoord (T : Over S) (φ : torusRing ZU X ⟶ Γ(T.left, ⊤)) : T ⟶ splitTorus S X :=
  Over.homMk (pullback.lift (T.left.toSpecΓ ≫ Spec.map φ) T.hom (specULiftZIsTerminal.hom_ext _ _))
    (pullback.lift_snd _ _ _)

variable {S} in
/- English proof (translation)
Establish `: (ofCoord T φ).left ≫ torusFst S X = T.left.toSpecΓ ≫ Spec.map φ` using `pullback.lift_fst _ _ _`. Rewrite using `[coord, this, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]`. Simplify using the standard rewrite rules.
-/
theorem coord_ofCoord (T : Over S) (φ : torusRing ZU X ⟶ Γ(T.left, ⊤)) :
    coord (ofCoord T φ) = φ := by
  have : (ofCoord T φ).left ≫ torusFst S X = T.left.toSpecΓ ≫ Spec.map φ := pullback.lift_fst _ _ _
  rw [coord, this, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  simp

variable {S} in

def ofChar (T : Over S) (g : Multiplicative X →* Γ(T.left, ⊤)) : T ⟶ splitTorus S X :=
  ofCoord T (CommRingCat.ofHom (AddMonoidAlgebra.liftNCRingHom
    ((Int.castRingHom _).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom) g
      fun _ _ => .all _ _))

variable {S} in
/- English proof (translation)
Rewrite using `[ofChar, coord_ofCoord]`. Simplify using `[AddMonoidAlgebra.liftNCRingHom]`.
-/
theorem coord_ofChar (T : Over S) (g : Multiplicative X →* Γ(T.left, ⊤)) (x : X) :
    (coord (ofChar T g)).hom (AddMonoidAlgebra.single x 1) = g (Multiplicative.ofAdd x) := by
  rw [ofChar, coord_ofCoord]
  simp [AddMonoidAlgebra.liftNCRingHom]

variable {S} in
/- English proof (translation)
Rewrite using `[← AddMonoidAlgebra.one_def, map_one]`.
-/
theorem coord_single_zero {T : Over S} (t : T ⟶ splitTorus S X) :
    (coord t).hom (AddMonoidAlgebra.single 0 1) = 1 := by
  rw [← AddMonoidAlgebra.one_def, map_one]

variable {S} in
/- English proof (translation)
Rewrite using `[← map_mul, AddMonoidAlgebra.single_mul_single, _root_.one_mul]`.
-/
theorem coord_single_add {T : Over S} (t : T ⟶ splitTorus S X) (x y : X) :
    (coord t).hom (AddMonoidAlgebra.single (x + y) 1) =
      (coord t).hom (AddMonoidAlgebra.single x 1) * (coord t).hom (AddMonoidAlgebra.single y 1) := by
  rw [← map_mul, AddMonoidAlgebra.single_mul_single, _root_.one_mul]

variable {S} in

/- English proof (translation)
Set `g : Multiplicative (X × X) →* Γ(T.left, ⊤)` to `{ toFun := fun z => (coord s).hom (AddMonoidAlgebra.single z.toAdd.1 1) * (coord t).hom (AddMonoidAlgebra.single z.toAdd.2 1) map_one' := by`. Express the relevant statement in the definitionally equal form `(coord s).hom (AddMonoidAlgebra.single 0 1) * (coord t).hom (AddMonoidAlgebra.single 0 1) = 1`. Rewrite using `[coord_single_zero, coord_single_zero, _root_.one_mul]`. Use the proof step `map_mul' := fun a b => by`. Rewrite using `[toAdd_mul, Prod.fst_add, Prod.snd_add, coord_single_add, coord_single_add]`.

Use `ring }`. Establish `hs : ofChar T g ≫ diagMap S (AddMonoidHom.inl X X) = s` using `hom_ext fun y => by`. Rewrite using `[coord_comp_diagMap_single, coord_ofChar]`. Express the relevant statement in the definitionally equal form `_ * (coord t).hom (AddMonoidAlgebra.single 0 1) = _`. Rewrite using `[coord_single_zero, _root_.mul_one]`.

Both sides reduce to the same expression. Establish `ht : ofChar T g ≫ diagMap S (AddMonoidHom.inr X X) = t` using `hom_ext fun y => by`. Rewrite using `[coord_comp_diagMap_single, coord_ofChar]`. Express the relevant statement in the definitionally equal form `(coord s).hom (AddMonoidAlgebra.single 0 1) * _ = _`. Rewrite using `[coord_single_zero, _root_.one_mul]`.

Both sides reduce to the same expression. Establish `: s * t = ofChar T g ≫ diagMap S (AddMonoidHom.inl X X + AddMonoidHom.inr X X)`. Rewrite using `[diagMap_add, MonObj.comp_mul, hs, ht]`. Rewrite using `[this, coord_comp_diagMap_single, coord_ofChar]`. Simplify using `[g]`.
-/
theorem coord_mul {T : Over S} (s t : T ⟶ splitTorus S X) (x : X) :
    (coord (s * t)).hom (AddMonoidAlgebra.single x 1) =
      (coord s).hom (AddMonoidAlgebra.single x 1) * (coord t).hom (AddMonoidAlgebra.single x 1) := by
  let g : Multiplicative (X × X) →* Γ(T.left, ⊤) :=
    { toFun := fun z => (coord s).hom (AddMonoidAlgebra.single z.toAdd.1 1) *
        (coord t).hom (AddMonoidAlgebra.single z.toAdd.2 1)
      map_one' := by
        change (coord s).hom (AddMonoidAlgebra.single 0 1) *
          (coord t).hom (AddMonoidAlgebra.single 0 1) = 1
        rw [coord_single_zero, coord_single_zero, _root_.one_mul]
      map_mul' := fun a b => by
        rw [toAdd_mul, Prod.fst_add, Prod.snd_add, coord_single_add, coord_single_add]
        ring }
  have hs : ofChar T g ≫ diagMap S (AddMonoidHom.inl X X) = s := hom_ext fun y => by
    rw [coord_comp_diagMap_single, coord_ofChar]
    change _ * (coord t).hom (AddMonoidAlgebra.single 0 1) = _
    rw [coord_single_zero, _root_.mul_one]; rfl
  have ht : ofChar T g ≫ diagMap S (AddMonoidHom.inr X X) = t := hom_ext fun y => by
    rw [coord_comp_diagMap_single, coord_ofChar]
    change (coord s).hom (AddMonoidAlgebra.single 0 1) * _ = _
    rw [coord_single_zero, _root_.one_mul]; rfl
  have : s * t = ofChar T g ≫ diagMap S (AddMonoidHom.inl X X + AddMonoidHom.inr X X) := by
    rw [diagMap_add, MonObj.comp_mul, hs, ht]
  rw [this, coord_comp_diagMap_single, coord_ofChar]
  simp [g]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `: (nsmulAddMonoidHom 0 : X →+ X) = 0` using `by ext; simp`. Rewrite using `[this, diagMap_zero]`. Both sides reduce to the same expression.

Consider the case `succ n ih`. Establish `: (nsmulAddMonoidHom (n + 1) : X →+ X) = nsmulAddMonoidHom n + AddMonoidHom.id X` using `by ext; simp [succ_nsmul]`. Rewrite using `[this, diagMap_add, ← ih, diagMap_id]`. Both sides reduce to the same expression.
-/
theorem mulN_eq_diagMap (n : ℕ) : mulN (splitTorus S X) n = diagMap S (nsmulAddMonoidHom n : X →+ X) := by
  induction n with
  | zero =>
    have : (nsmulAddMonoidHom 0 : X →+ X) = 0 := by ext; simp
    rw [this, diagMap_zero]; rfl
  | succ n ih =>
    have : (nsmulAddMonoidHom (n + 1) : X →+ X) = nsmulAddMonoidHom n + AddMonoidHom.id X := by
      ext; simp [succ_nsmul]
    rw [this, diagMap_add, ← ih, diagMap_id]; rfl

/- English proof (translation)
Establish `hw : diagMap S q ≫ diagMap S u = toUnit _ ≫ η`. Establish `: q.comp u = 0` using `by ext y; exact (h _).2 ⟨y, rfl⟩`. Rewrite using `[← diagMap_comp, this, diagMap_zero]`. Both sides reduce to the same expression. Establish `hmono : ∀ {T : Over S} {a b : T ⟶ splitTorus S Z}, a ≫ diagMap S q = b ≫ diagMap S q → a = b`.

Introduce `T a b hab`. Use `hom_ext fun z => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hq z`. Rewrite using `[← coord_comp_diagMap_single, hab, coord_comp_diagMap_single]`. Use `isPullback_toUnit_of_lift S hw hmono fun {T} t ht => ?_` and prove the remaining obligations.

Establish `h1 : ∀ y, (coord t).hom (AddMonoidAlgebra.single (u y) 1) = 1` using `fun y => by`. Rewrite using `[← coord_comp_diagMap_single, ht]`. Conclude with `coord_one T y`. Establish `h2 : ∀ x x', q x = q x' → (coord t).hom (AddMonoidAlgebra.single x 1) = (coord t).hom (AddMonoidAlgebra.single x' 1)` using `fun x x' hx => by`. Take `⟨y, hy⟩` from `(h (x - x')).1 (by rw [map_sub, hx, sub_self])`.

Rewrite using `[show x = u y + x' by rw [hy, sub_add_cancel], ← _root_.one_mul (1 : ZU.{u}), ← AddMonoidAlgebra.single_mul_single, map_mul, h1, _root_.one_mul, _root_.one_mul]`. Set `σ` to `Function.surjInv hq`. Establish `hσ : ∀ z, q (σ z) = z` using `Function.surjInv_eq hq`. Set `g : Multiplicative Z →* Γ(T.left, ⊤)` to `{ toFun := fun z => (coord t).hom (AddMonoidAlgebra.single (σ z.toAdd) 1) map_one' := by`. Rewrite using `[h2 _ 0 (by rw [hσ, _root_.map_zero]; rfl), ← AddMonoidAlgebra.one_def, map_one]`.

Use the proof step `map_mul' := fun a b => by`. Rewrite using `[← map_mul, AddMonoidAlgebra.single_mul_single, _root_.one_mul]`. Conclude with `h2 _ _ (by rw [_root_.map_add, hσ, hσ, hσ]; rfl) }`. Set `c : ULift.{u} ℤ →+* Γ(T.left, ⊤)` to `(Int.castRingHom _).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom`. Set `φ : AddMonoidAlgebra (ULift.{u} ℤ) Z →+* Γ(T.left, ⊤)` to `AddMonoidAlgebra.liftNCRingHom c g fun _ _ => .all _ _`.

Use `⟨ofCoord T (CommRingCat.ofHom φ), hom_ext fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[coord_comp_diagMap_single, coord_ofCoord]`. Establish `: φ (AddMonoidAlgebra.single (q x) 1) = g (Multiplicative.ofAdd (q x))`. Simplify using `[φ, AddMonoidAlgebra.liftNCRingHom]`. Conclude with `this.trans (h2 _ _ (hσ _))`.
-/
theorem isPullback_of_exact (u : Y →+ X) (q : X →+ Z) (hq : Function.Surjective q)
    (h : Function.Exact u q) :
    IsPullback (diagMap S q) (toUnit _) (diagMap S u) (η : 𝟙_ (Over S) ⟶ splitTorus S Y) := by
  have hw : diagMap S q ≫ diagMap S u = toUnit _ ≫ η := by
    have : q.comp u = 0 := by ext y; exact (h _).2 ⟨y, rfl⟩
    rw [← diagMap_comp, this, diagMap_zero]; rfl
  have hmono : ∀ {T : Over S} {a b : T ⟶ splitTorus S Z}, a ≫ diagMap S q = b ≫ diagMap S q → a = b := by
    intro T a b hab
    refine hom_ext fun z => ?_
    obtain ⟨x, rfl⟩ := hq z
    rw [← coord_comp_diagMap_single, hab, coord_comp_diagMap_single]
  refine isPullback_toUnit_of_lift S hw hmono fun {T} t ht => ?_
  have h1 : ∀ y, (coord t).hom (AddMonoidAlgebra.single (u y) 1) = 1 := fun y => by
    rw [← coord_comp_diagMap_single, ht]; exact coord_one T y
  have h2 : ∀ x x', q x = q x' → (coord t).hom (AddMonoidAlgebra.single x 1) =
      (coord t).hom (AddMonoidAlgebra.single x' 1) := fun x x' hx => by
    obtain ⟨y, hy⟩ := (h (x - x')).1 (by rw [map_sub, hx, sub_self])
    rw [show x = u y + x' by rw [hy, sub_add_cancel], ← _root_.one_mul (1 : ZU.{u}),
      ← AddMonoidAlgebra.single_mul_single, map_mul, h1, _root_.one_mul, _root_.one_mul]
  let σ := Function.surjInv hq
  have hσ : ∀ z, q (σ z) = z := Function.surjInv_eq hq
  let g : Multiplicative Z →* Γ(T.left, ⊤) :=
    { toFun := fun z => (coord t).hom (AddMonoidAlgebra.single (σ z.toAdd) 1)
      map_one' := by
        rw [h2 _ 0 (by rw [hσ, _root_.map_zero]; rfl), ← AddMonoidAlgebra.one_def, map_one]
      map_mul' := fun a b => by
        rw [← map_mul, AddMonoidAlgebra.single_mul_single, _root_.one_mul]
        exact h2 _ _ (by rw [_root_.map_add, hσ, hσ, hσ]; rfl) }
  let c : ULift.{u} ℤ →+* Γ(T.left, ⊤) :=
    (Int.castRingHom _).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom
  let φ : AddMonoidAlgebra (ULift.{u} ℤ) Z →+* Γ(T.left, ⊤) :=
    AddMonoidAlgebra.liftNCRingHom c g fun _ _ => .all _ _
  refine ⟨ofCoord T (CommRingCat.ofHom φ), hom_ext fun x => ?_⟩
  rw [coord_comp_diagMap_single, coord_ofCoord]
  have : φ (AddMonoidAlgebra.single (q x) 1) = g (Multiplicative.ofAdd (q x)) := by
    simp [φ, AddMonoidAlgebra.liftNCRingHom]
  exact this.trans (h2 _ _ (hσ _))

/- English proof (translation)
The claim follows from `isPullback_of_exact S u _ (QuotientAddGroup.mk'_surjective _) fun x => QuotientAddGroup.eq_zero_iff x`.
-/
theorem isPullback_ker (u : Y →+ X) :
    IsPullback (diagMap S (QuotientAddGroup.mk' u.range)) (toUnit _) (diagMap S u)
      (η : 𝟙_ (Over S) ⟶ splitTorus S Y) :=
  isPullback_of_exact S u _ (QuotientAddGroup.mk'_surjective _) fun x =>
    QuotientAddGroup.eq_zero_iff x

/- English proof (translation)
Rewrite using `[mulN_eq_diagMap]`. Conclude with `isPullback_ker S _`.
-/
theorem isPullback_torsion (n : ℕ) :
    IsPullback (diagMap S (QuotientAddGroup.mk' (nsmulAddMonoidHom n : X →+ X).range)) (toUnit _)
      (mulN (splitTorus S X) n) (η : 𝟙_ (Over S) ⟶ splitTorus S X) := by
  rw [mulN_eq_diagMap]; exact isPullback_ker S _

variable (X) in

def torsionIso (n : ℕ) :
    torsion (splitTorus S X) n ≅ splitTorus S (X ⧸ (nsmulAddMonoidHom n : X →+ X).range) :=
  (isPullback_torsion S n).isoPullback.symm

/- English proof (translation)
The claim follows from `(isPullback_torsion S n).isoPullback_hom_fst`.
-/
theorem torsionIso_inv_ι (n : ℕ) : (torsionIso S X n).inv ≫ torsion.ι _ n =
    diagMap S (QuotientAddGroup.mk' (nsmulAddMonoidHom n : X →+ X).range) :=
  (isPullback_torsion S n).isoPullback_hom_fst

/- English proof (translation)
The claim follows from `(isPullback_torsion S n).isoPullback_inv_fst`.
-/
theorem torsionIso_hom_diagMap (n : ℕ) : (torsionIso S X n).hom ≫
    diagMap S (QuotientAddGroup.mk' (nsmulAddMonoidHom n : X →+ X).range) = torsion.ι _ n :=
  (isPullback_torsion S n).isoPullback_inv_fst

/- English proof (translation)
The claim follows from `P.of_isPullback (isPullback_diagMap S u) h`.
-/
theorem of_ringMap (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] (u : Y →+ X)
    (h : P (Spec.map (ringMap u))) : P (diagMap S u).left :=
  P.of_isPullback (isPullback_diagMap S u) h

instance isAffineHom_diagMap (u : Y →+ X) : IsAffineHom (diagMap S u).left :=
  of_ringMap S @IsAffineHom u inferInstance

/- English proof (translation)
The claim follows from `of_ringMap S @IsClosedImmersion u (IsClosedImmersion.spec_of_surjective _ (GroupAlg.surjective_of_surjective _ u hu))`.
-/
theorem isClosedImmersion_diagMap {u : Y →+ X} (hu : Function.Surjective u) :
    IsClosedImmersion (diagMap S u).left :=
  of_ringMap S @IsClosedImmersion u
    (IsClosedImmersion.spec_of_surjective _ (GroupAlg.surjective_of_surjective _ u hu))

/- English proof (translation)
The claim follows from `Flat.SpecMap_iff.2 (GroupAlg.faithfullyFlat_of_injective _ u hu).flat`.
-/
theorem flat_ringMap {u : Y →+ X} (hu : Function.Injective u) : Flat (Spec.map (ringMap u)) :=
  Flat.SpecMap_iff.2 (GroupAlg.faithfullyFlat_of_injective _ u hu).flat

/- English proof (translation)
The claim follows from `of_ringMap S @Flat u (flat_ringMap hu)`.
-/
theorem flat_diagMap {u : Y →+ X} (hu : Function.Injective u) : Flat (diagMap S u).left :=
  of_ringMap S @Flat u (flat_ringMap hu)

/- English proof (translation)
The claim follows from `of_ringMap S @Surjective u ⟨(RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.1 (GroupAlg.faithfullyFlat_of_injective _ u hu)).2⟩`.
-/
theorem surjective_diagMap {u : Y →+ X} (hu : Function.Injective u) : Surjective (diagMap S u).left :=
  of_ringMap S @Surjective u
    ⟨(RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.1
      (GroupAlg.faithfullyFlat_of_injective _ u hu)).2⟩

/- English proof (translation)
The claim follows from `(IsFinite.SpecMap_iff _).2 (GroupAlg.finite_of_finiteIndex _ u)`.
-/
theorem isFinite_ringMap (u : Y →+ X) [u.range.FiniteIndex] : IsFinite (Spec.map (ringMap u)) :=
  (IsFinite.SpecMap_iff _).2 (GroupAlg.finite_of_finiteIndex _ u)

/- English proof (translation)
The claim follows from `of_ringMap S @IsFinite u (isFinite_ringMap u)`.
-/
theorem isFinite_diagMap (u : Y →+ X) [u.range.FiniteIndex] : IsFinite (diagMap S u).left :=
  of_ringMap S @IsFinite u (isFinite_ringMap u)

/- English proof (translation)
The claim follows from `of_ringMap S @LocallyOfFinitePresentation u ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 (GroupAlg.finitePresentation_of_injective _ u hu))`.
-/
theorem locallyOfFinitePresentation_diagMap {u : Y →+ X} (hu : Function.Injective u)
    [u.range.FiniteIndex] : LocallyOfFinitePresentation (diagMap S u).left :=
  of_ringMap S @LocallyOfFinitePresentation u
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      (GroupAlg.finitePresentation_of_injective _ u hu))

/- English proof (translation)
Use `flat_ringMap hu` as an intermediate fact. Use `isFinite_ringMap u` as an intermediate fact. Rewrite using `[Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_diagMap S u), Scheme.Hom.finrank_SpecMap_eq_finrank (GroupAlg.finite_of_finiteIndex _ u) (GroupAlg.faithfullyFlat_of_injective _ u hu).flat]`. Conclude with `GroupAlg.finrank_of_injective _ u hu _`.
-/
theorem finrank_diagMap {u : Y →+ X} (hu : Function.Injective u) [u.range.FiniteIndex]
    (y : (splitTorus S Y).left) : (diagMap S u).left.finrank y = u.range.index := by
  have := flat_ringMap hu
  have := isFinite_ringMap u
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_diagMap S u),
    Scheme.Hom.finrank_SpecMap_eq_finrank (GroupAlg.finite_of_finiteIndex _ u)
      (GroupAlg.faithfullyFlat_of_injective _ u hu).flat]
  exact GroupAlg.finrank_of_injective _ u hu _

section Affine

variable (R : Type u) [CommRing R] (X : Type u) [AddCommGroup X]

abbrev intAlgebra : Algebra ZU.{u} R := ULift.algebra' ℤ R

attribute [local instance] intAlgebra
open scoped AlgebraMonoidAlgebra

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun r a b => by obtain ⟨n⟩ := r change (n • a) • b = n • (a • b) simp only [Algebra.smul_def, map_mul, _root_.mul_assoc, eq_intCast, map_intCast]⟩`.
-/
theorem isScalarTower_groupRing :
    IsScalarTower ZU.{u} (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra R X) :=
  ⟨fun r a b => by
    obtain ⟨n⟩ := r
    change (n • a) • b = n • (a • b)
    simp only [Algebra.smul_def, map_mul, _root_.mul_assoc, eq_intCast, map_intCast]⟩

/- English proof (translation)
Use `isScalarTower_groupRing R X` as an intermediate fact. Establish `: Algebra.IsPushout ZU.{u} (AddMonoidAlgebra ZU.{u} X) R (AddMonoidAlgebra R X)` using `AddMonoidAlgebra.instIsPushout'`. Rewrite using `[show toZ (Spec (.of R)) = Spec.map (CommRingCat.ofHom (algebraMap ZU.{u} R)) from specULiftZIsTerminal.hom_ext _ _]`. Conclude with `isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout ZU.{u} (AddMonoidAlgebra ZU.{u} X) R (AddMonoidAlgebra R X))`.
-/
theorem isPullback_groupRing :
    IsPullback (Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom X (algebraMap ZU.{u} R))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))))
      (splitTorusAff ZU X).hom (toZ (Spec (.of R))) := by
  have := isScalarTower_groupRing R X
  have : Algebra.IsPushout ZU.{u} (AddMonoidAlgebra ZU.{u} X) R (AddMonoidAlgebra R X) :=
    AddMonoidAlgebra.instIsPushout'
  rw [show toZ (Spec (.of R)) = Spec.map (CommRingCat.ofHom (algebraMap ZU.{u} R)) from
    specULiftZIsTerminal.hom_ext _ _]
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout ZU.{u} (AddMonoidAlgebra ZU.{u} X) R (AddMonoidAlgebra R X))

variable {S R} in

/- English proof (translation)
Establish `h` using `isPullback_groupRing R X`. Use `⟨h.lift (torusFst S X) ((splitTorus S X).hom ≫ g) (specULiftZIsTerminal.hom_ext _ _), IsPullback.of_right ?_ (h.lift_snd _ _ _) h⟩` and prove the remaining obligations. Rewrite using `[h.lift_fst, show g ≫ toZ (Spec (.of R)) = toZ S from specULiftZIsTerminal.hom_ext _ _]`. Conclude with `isPullback_torusFst S X`.
-/
theorem exists_isPullback (g : S ⟶ Spec (.of R)) :
    ∃ a : (splitTorus S X).left ⟶ Spec (.of (AddMonoidAlgebra R X)),
      IsPullback a (splitTorus S X).hom
        (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X)))) g := by
  have h := isPullback_groupRing R X
  refine ⟨h.lift (torusFst S X) ((splitTorus S X).hom ≫ g) (specULiftZIsTerminal.hom_ext _ _),
    IsPullback.of_right ?_ (h.lift_snd _ _ _) h⟩
  rw [h.lift_fst, show g ≫ toZ (Spec (.of R)) = toZ S from specULiftZIsTerminal.hom_ext _ _]
  exact isPullback_torusFst S X

end Affine

/- English proof (translation)
The claim follows from `P.of_isPullback (isPullback_torusFst S X) h`.
-/
theorem of_affine (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] (X : Type u)
    [AddCommGroup X]
    (h : P (Spec.map (CommRingCat.ofHom (algebraMap ZU.{u} (AddMonoidAlgebra ZU.{u} X))))) :
    P (splitTorus S X).hom :=
  P.of_isPullback (isPullback_torusFst S X) h

instance isAffineHom_hom (X : Type u) [AddCommGroup X] : IsAffineHom (splitTorus S X).hom :=
  of_affine S @IsAffineHom X inferInstance

instance flat_hom (X : Type u) [AddCommGroup X] : Flat (splitTorus S X).hom :=
  of_affine S @Flat X (Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance))

instance surjective_hom (X : Type u) [AddCommGroup X] : Surjective (splitTorus S X).hom :=
  ⟨fun s => ⟨(η : 𝟙_ (Over S) ⟶ splitTorus S X).left s, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩

instance locallyOfFinitePresentation_hom (X : Type u) [AddCommGroup X] [Module.Finite ℤ X] :
    LocallyOfFinitePresentation (splitTorus S X).hom := by
  refine of_affine S @LocallyOfFinitePresentation X
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 ?_)
  have : IsNoetherianRing ZU.{u} :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm
  have : AddGroup.FG X := Module.Finite.iff_addGroup_fg.1 ‹_›
  have : AddMonoid.FG X := AddGroup.fg_iff_addMonoid_fg.1 this
  exact RingHom.finitePresentation_algebraMap.2
    (Algebra.FinitePresentation.of_finiteType.1 inferInstance)

instance isFinite_hom (X : Type u) [AddCommGroup X] [Finite X] : IsFinite (splitTorus S X).hom :=
  of_affine S @IsFinite X ((IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance))

/- English proof (translation)
Take `⟨a, h⟩` from `exists_isPullback X (toZ S)`. Establish `: IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ZU.{u} (AddMonoidAlgebra ZU.{u} X))))` using `(IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)`. Establish `: Flat (Spec.map (CommRingCat.ofHom (algebraMap ZU.{u} (AddMonoidAlgebra ZU.{u} X))))` using `Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)`. Rewrite using `[Scheme.Hom.finrank_of_isPullback _ _ _ _ h]`. Use `(Scheme.Hom.finrank_SpecMap_algebraMap ZU.{u} (AddMonoidAlgebra ZU.{u} X) _).trans ?_` and prove the remaining obligations.

Rewrite using `[Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_nat_card_basis (AddMonoidAlgebra.basis X ZU.{u})]`. Both sides reduce to the same expression.
-/
theorem finrank_hom (X : Type u) [AddCommGroup X] [Finite X] (s : S) :
    (splitTorus S X).hom.finrank s = Nat.card X := by
  obtain ⟨a, h⟩ := exists_isPullback X (toZ S)
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ZU.{u} (AddMonoidAlgebra ZU.{u} X)))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap ZU.{u} (AddMonoidAlgebra ZU.{u} X)))) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ h]
  refine (Scheme.Hom.finrank_SpecMap_algebraMap ZU.{u} (AddMonoidAlgebra ZU.{u} X) _).trans ?_
  rw [Module.rankAtStalk_eq_finrank_of_free,
    Module.finrank_eq_nat_card_basis (AddMonoidAlgebra.basis X ZU.{u})]
  rfl

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_isPullback (R := Γ(S, ⊤)) X S.toSpecΓ`. Use `MorphismProperty.of_isPullback (P := @Etale) ha ((HasRingHomProperty.Spec_iff (P := @Etale)).2 ?_)` and prove the remaining obligations. Conclude with `RingHom.etale_algebraMap.2 (GroupAlg.etale_of_isUnit_card _ h)`.
-/
theorem etale_hom (X : Type u) [AddCommGroup X] [Finite X] (h : IsUnit (Nat.card X : Γ(S, ⊤))) :
    Etale (splitTorus S X).hom := by
  obtain ⟨a, ha⟩ := exists_isPullback (R := Γ(S, ⊤)) X S.toSpecΓ
  refine MorphismProperty.of_isPullback (P := @Etale) ha
    ((HasRingHomProperty.Spec_iff (P := @Etale)).2 ?_)
  exact RingHom.etale_algebraMap.2 (GroupAlg.etale_of_isUnit_card _ h)

instance geometricallyIntegral_hom (X : Type u) [AddCommGroup X] [UniqueSums X] :
    GeometricallyIntegral (splitTorus S X).hom := by
  refine ⟨fun K _ y W fst snd h => ?_⟩
  have h2 := h.paste_horiz (isPullback_torusFst S X)
  rw [show y ≫ toZ S = toZ _ from specULiftZIsTerminal.hom_ext _ _] at h2
  have : IsDomain (AddMonoidAlgebra K X) := NoZeroDivisors.to_isDomain _
  exact IsIntegral.of_isIso ((isPullback_groupRing K X).isoIsPullback _ _ h2).hom

instance geometricallyConnected_hom (X : Type u) [AddCommGroup X] [UniqueSums X] :
    GeometricallyConnected (splitTorus S X).hom :=
  ⟨fun _ _ y _ fst snd h =>
    have := (geometricallyIntegral_hom S X).1 y fst snd h
    inferInstance⟩

section Mul

variable (X : Type u) [AddCommGroup X] {n : ℕ}

/- English proof (translation)
Establish `: IsAddTorsionFree X` using `Module.isTorsionFree_int_iff_isAddTorsionFree.1 inferInstance`. Conclude with `nsmul_right_injective hn`.
-/
theorem nsmul_injective [Module.Free ℤ X] (hn : n ≠ 0) :
    Function.Injective (nsmulAddMonoidHom n : X →+ X) := by
  have : IsAddTorsionFree X := Module.isTorsionFree_int_iff_isAddTorsionFree.1 inferInstance
  exact nsmul_right_injective hn

/- English proof (translation)
Establish `: AddGroup.FG X` using `Module.Finite.iff_addGroup_fg.1 ‹_›`. Conclude with `AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg X hn`.
-/
theorem finiteIndex_nsmul [Module.Finite ℤ X] (hn : n ≠ 0) :
    (nsmulAddMonoidHom n : X →+ X).range.FiniteIndex := by
  have : AddGroup.FG X := Module.Finite.iff_addGroup_fg.1 ‹_›
  exact AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg X hn

/- English proof (translation)
Use `finiteIndex_nsmul X hn` as an intermediate fact. Rewrite using `[mulN_eq_diagMap]`. Conclude with `isFinite_diagMap S _`.
-/
theorem isFinite_mulN [Module.Finite ℤ X] (hn : n ≠ 0) :
    IsFinite (mulN (splitTorus S X) n).left := by
  have := finiteIndex_nsmul X hn
  rw [mulN_eq_diagMap]; exact isFinite_diagMap S _

/- English proof (translation)
Rewrite using `[mulN_eq_diagMap]`. Conclude with `flat_diagMap S (nsmul_injective X hn)`.
-/
theorem flat_mulN [Module.Free ℤ X] (hn : n ≠ 0) : Flat (mulN (splitTorus S X) n).left := by
  rw [mulN_eq_diagMap]; exact flat_diagMap S (nsmul_injective X hn)

/- English proof (translation)
Rewrite using `[mulN_eq_diagMap]`. Conclude with `surjective_diagMap S (nsmul_injective X hn)`.
-/
theorem surjective_mulN [Module.Free ℤ X] (hn : n ≠ 0) :
    Surjective (mulN (splitTorus S X) n).left := by
  rw [mulN_eq_diagMap]; exact surjective_diagMap S (nsmul_injective X hn)

/- English proof (translation)
Use `finiteIndex_nsmul X hn` as an intermediate fact. Rewrite using `[mulN_eq_diagMap]`. Conclude with `locallyOfFinitePresentation_diagMap S (nsmul_injective X hn)`.
-/
theorem locallyOfFinitePresentation_mulN [Module.Free ℤ X] [Module.Finite ℤ X] (hn : n ≠ 0) :
    LocallyOfFinitePresentation (mulN (splitTorus S X) n).left := by
  have := finiteIndex_nsmul X hn
  rw [mulN_eq_diagMap]; exact locallyOfFinitePresentation_diagMap S (nsmul_injective X hn)

/- English proof (translation)
Use `finiteIndex_nsmul X hn` as an intermediate fact. Rewrite using `[mulN_eq_diagMap, finrank_diagMap S (nsmul_injective X hn), AddSubgroup.index_range_nsmul]`.
-/
theorem finrank_mulN [Module.Free ℤ X] [Module.Finite ℤ X] (hn : n ≠ 0)
    (y : (splitTorus S X).left) :
    (mulN (splitTorus S X) n).left.finrank y = n ^ Module.finrank ℤ X := by
  have := finiteIndex_nsmul X hn
  rw [mulN_eq_diagMap, finrank_diagMap S (nsmul_injective X hn), AddSubgroup.index_range_nsmul]

end Mul

section BaseChange

variable {S} {S' : Scheme.{u}} (f : S' ⟶ S)

/- English proof (translation)
Rewrite using `[show toZ S' = f ≫ toZ S from specULiftZIsTerminal.hom_ext _ _]`. Conclude with `(IsPullback.of_hasPullback _ _).paste_horiz (isPullback_torusFst S X)`.
-/
theorem isPullback_baseChange (X : Type u) [AddCommGroup X] :
    IsPullback (pullback.fst (splitTorus S X).hom f ≫ torusFst S X)
      ((Over.pullback f).obj (splitTorus S X)).hom (splitTorusAff ZU X).hom (toZ S') := by
  rw [show toZ S' = f ≫ toZ S from specULiftZIsTerminal.hom_ext _ _]
  exact (IsPullback.of_hasPullback _ _).paste_horiz (isPullback_torusFst S X)

def baseChangeIso (X : Type u) [AddCommGroup X] :
    (Over.pullback f).obj (splitTorus S X) ≅ splitTorus S' X :=
  Over.isoMk (isPullback_baseChange f X).isoPullback
    (isPullback_baseChange f X).isoPullback_hom_snd

/- English proof (translation)
The claim follows from `(isPullback_baseChange f X).isoPullback_hom_fst`.
-/
theorem baseChangeIso_hom_torusFst (X : Type u) [AddCommGroup X] :
    (baseChangeIso f X).hom.left ≫ torusFst S' X =
      pullback.fst (splitTorus S X).hom f ≫ torusFst S X :=
  (isPullback_baseChange f X).isoPullback_hom_fst

omit [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] in

/- English proof (translation)
Substitute `e` using the available equality. Set `m` to `(Functor.mapMonNatIso (Over.pullbackComp f h) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)`. Establish `hφ' : φ = m.inv.hom` using `by ext1`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[hφ]`.

Simplify using `[m, Over.pullbackComp]`. Use `erw [Category.id_comp]`. Simplify using `[Over.mapComp, pullback.lift_fst_assoc, pullback.lift_fst]`. Conclude with `(Over.w φ).trans (Over.w m.inv.hom).symm`. Rewrite using `[hφ']`.

Conclude with `m.inv.isMonHom_hom`.
-/
theorem isMonHom_of_comp {B : Scheme.{u}} (h : S ⟶ B) (g : S' ⟶ B) (e : g = f ≫ h) (G : Over B)
    [GrpObj G] (φ : (Over.pullback f).obj ((Over.pullback h).obj G) ⟶ (Over.pullback g).obj G)
    (hφ : φ.left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _) : IsMonHom φ := by
  subst e
  let m := (Functor.mapMonNatIso (Over.pullbackComp f h) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
  have hφ' : φ = m.inv.hom := by
    ext1
    apply pullback.hom_ext
    · rw [hφ]
      simp [m, Over.pullbackComp]
      erw [Category.id_comp]
      simp [Over.mapComp, pullback.lift_fst_assoc, pullback.lift_fst]
    · exact (Over.w φ).trans (Over.w m.inv.hom).symm
  rw [hφ']
  exact m.inv.isMonHom_hom

instance baseChangeIso_isMonHom (X : Type u) [AddCommGroup X] : IsMonHom (baseChangeIso f X).hom :=
  isMonHom_of_comp f (toZ S) (toZ S') (specULiftZIsTerminal.hom_ext _ _) _ _
    (baseChangeIso_hom_torusFst f X)

/- English proof (translation)
Use `ext1`. Apply `(isPullback_torusFst S' Y).hom_ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, diagMap_left_torusFst, baseChangeIso_hom_torusFst, reassoc_of% baseChangeIso_hom_torusFst f X, ← diagMap_left_torusFst]`. Conclude with `pullback.lift_fst_assoc _ _ _ _ |>.trans (Category.assoc _ _ _)`. Rewrite using `[Over.w, Over.w]`.
-/
theorem baseChangeIso_naturality (u : Y →+ X) :
    (Over.pullback f).map (diagMap S u) ≫ (baseChangeIso f Y).hom =
      (baseChangeIso f X).hom ≫ diagMap S' u := by
  ext1
  apply (isPullback_torusFst S' Y).hom_ext
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, diagMap_left_torusFst,
      baseChangeIso_hom_torusFst, reassoc_of% baseChangeIso_hom_torusFst f X, ← diagMap_left_torusFst]
    exact pullback.lift_fst_assoc _ _ _ _ |>.trans (Category.assoc _ _ _)
  · rw [Over.w, Over.w]

end BaseChange

/- English proof (translation)
Take `⟨s⟩` from `‹Nonempty S›`. Introduce `a b hab`. Set `K` to `S.residueField s`. Set `p : Spec K ⟶ S` to `S.fromSpecResidueField s`. Set `φ : torusRing ZU X ⟶ CommRingCat.of (AddMonoidAlgebra K X)` to `CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom X ((Int.castRingHom K).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom))`.

Set `T : Over S` to `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X))) ≫ p)`. Set `t : T ⟶ splitTorus S X` to `ofCoord T (φ ≫ (Scheme.ΓSpecIso _).inv)`. Establish `h1 : ∀ x, (coord t).hom (AddMonoidAlgebra.single x 1) = t.left.appTop.hom (chi X x)` using `fun x => by rw [← Category.comp_id t, coord_comp, Category.comp_id]; rfl`. Establish `h2` using `(h1 a).trans ((congrArg _ hab).trans (h1 b).symm)`. Rewrite `h2` using `[coord_ofCoord]`.

Establish `h3 : φ.hom (AddMonoidAlgebra.single a 1) = φ.hom (AddMonoidAlgebra.single b 1)` using `(cr_iso_bij (Scheme.ΓSpecIso (.of (AddMonoidAlgebra K X))).symm).1 h2`. Simplify using `only [φ, CommRingCat.hom_ofHom, AddMonoidAlgebra.mapRingHom_single, map_one] at h3`. Conclude with `AddMonoidAlgebra.single_left_injective one_ne_zero h3`.
-/
theorem chi_injective [Nonempty S] : Function.Injective (chi (S := S) X) := by
  obtain ⟨s⟩ := ‹Nonempty S›
  intro a b hab
  let K := S.residueField s
  let p : Spec K ⟶ S := S.fromSpecResidueField s
  let φ : torusRing ZU X ⟶ CommRingCat.of (AddMonoidAlgebra K X) :=
    CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom X
      ((Int.castRingHom K).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom))
  let T : Over S := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X))) ≫ p)
  let t : T ⟶ splitTorus S X := ofCoord T (φ ≫ (Scheme.ΓSpecIso _).inv)
  have h1 : ∀ x, (coord t).hom (AddMonoidAlgebra.single x 1) = t.left.appTop.hom (chi X x) :=
    fun x => by rw [← Category.comp_id t, coord_comp, Category.comp_id]; rfl
  have h2 := (h1 a).trans ((congrArg _ hab).trans (h1 b).symm)
  rw [coord_ofCoord] at h2
  have h3 : φ.hom (AddMonoidAlgebra.single a 1) = φ.hom (AddMonoidAlgebra.single b 1) :=
    (cr_iso_bij (Scheme.ΓSpecIso (.of (AddMonoidAlgebra K X))).symm).1 h2
  simp only [φ, CommRingCat.hom_ofHom, AddMonoidAlgebra.mapRingHom_single, map_one] at h3
  exact AddMonoidAlgebra.single_left_injective one_ne_zero h3

/- English proof (translation)
Introduce `u v h`. Use extensionality with `y`. Apply `chi_injective S` to reduce the goal to its premises. Rewrite using `[chi, chi, ← coord_comp_diagMap_single, h, coord_comp_diagMap_single]`.
-/
theorem diagMap_injective [Nonempty S] :
    Function.Injective (diagMap S : (Y →+ X) → (splitTorus S X ⟶ splitTorus S Y)) := by
  intro u v h
  ext y
  apply chi_injective S
  rw [chi, chi, ← coord_comp_diagMap_single, h, coord_comp_diagMap_single]

/- English proof (translation)
Rewrite using `[← diagMap_id, ← diagMap_zero]`. Introduce `h`. Take `⟨x, hx⟩` from `exists_ne (0 : X)`. Conclude with `hx (DFunLike.congr_fun (diagMap_injective S h) x)`.
-/
theorem id_ne_one [Nonempty S] [Nontrivial X] : 𝟙 (splitTorus S X) ≠ 1 := by
  rw [← diagMap_id, ← diagMap_zero]
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  exact hx (DFunLike.congr_fun (diagMap_injective S h) x)

end GlobalTheory.Diag

namespace GlobalTheory.Diag

variable (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

instance smoothOfRelativeDimension_hom :
    SmoothOfRelativeDimension (Module.finrank ℤ X) (splitTorus S X).hom :=
  ReciprocityTheory.ChartRestriction.G.H1.torus_dim S X

instance smooth_hom : Smooth (splitTorus S X).hom :=
  (smoothOfRelativeDimension_hom S X).smooth

/- English proof (translation)
The claim follows from `(ReciprocityTheory.ChartRestriction.G.Out.Inh.zeroPolAV S).isAb`.
-/
theorem isAbelianScheme_unit : IsAbelianScheme (𝟙_ (Over S)) :=
  (ReciprocityTheory.ChartRestriction.G.Out.Inh.zeroPolAV S).isAb

def torusExtension {K : Type} [Field K] (p : Spec (.of K) ⟶ S) :
    TorusExtension ((Over.pullback p).obj (splitTorus S X)) where
  X := X
  B := 𝟙_ _
  isAbelian := isAbelianScheme_unit _
  q := toUnit _
  q_hom := inferInstance
  q_flat := by rw [toUnit_left]; exact inferInstanceAs (Flat (pullback.snd _ _))
  q_surjective := by rw [toUnit_left]; exact inferInstanceAs (Surjective (pullback.snd _ _))
  q_quasiCompact := by rw [toUnit_left]; exact inferInstanceAs (QuasiCompact (pullback.snd _ _))
  i := (baseChangeIso p X).inv
  i_hom := inferInstance
  isKernel := isPullback_toUnit_of_lift _ (toUnit_unique _ _) (fun h => (cancel_mono _).1 h)
    fun t _ => ⟨t ≫ (baseChangeIso p X).hom, by simp⟩

instance isSemiAbelian : IsSemiAbelian (splitTorus S X) where
  comm := inferInstance
  smooth := inferInstance
  separated := inferInstance
  quasiCompact := inferInstance
  geomConnected := inferInstance
  fibres := fun _ _ _ p => ⟨torusExtension S X p⟩

omit [Module.Free ℤ X] [Module.Finite ℤ X] in

/- English proof (translation)
Take `⟨h₁, h₂⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback (splitTorus S X) f`. Use `⟨?_, fun T x y x₀ y₀ hx hy => ?_⟩` and prove the remaining obligations. Establish `: IsIso (baseChangeIso f X).inv.left` using `inferInstanceAs (IsIso ((Over.forget _).map (baseChangeIso f X).inv))`. Establish `h : IsPullback (baseChangeIso f X).inv.left (splitTorus S' X).hom ((Over.pullback f).obj (splitTorus S X)).hom (𝟙 _)` using `IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩`. Simplify using `using h.paste_horiz h₁`.

Rewrite using `[h₂ T (x ≫ (baseChangeIso f X).inv) (y ≫ (baseChangeIso f X).inv) x₀ y₀ (by rw [hx, Over.comp_left, Category.assoc]) (by rw [hy, Over.comp_left, Category.assoc]), ← MonObj.mul_comp, Over.comp_left, Category.assoc]`.
-/
theorem isGrpPullback {S S' : Scheme.{0}} (f : S' ⟶ S) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback (splitTorus S' X) (splitTorus S X) f
      ((baseChangeIso f X).inv.left ≫ pullback.fst (splitTorus S X).hom f) := by
  obtain ⟨h₁, h₂⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback (splitTorus S X) f
  refine ⟨?_, fun T x y x₀ y₀ hx hy => ?_⟩
  · have : IsIso (baseChangeIso f X).inv.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (baseChangeIso f X).inv))
    have h : IsPullback (baseChangeIso f X).inv.left (splitTorus S' X).hom
        ((Over.pullback f).obj (splitTorus S X)).hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
    simpa using h.paste_horiz h₁
  · rw [h₂ T (x ≫ (baseChangeIso f X).inv) (y ≫ (baseChangeIso f X).inv) x₀ y₀
      (by rw [hx, Over.comp_left, Category.assoc]) (by rw [hy, Over.comp_left, Category.assoc]),
      ← MonObj.mul_comp, Over.comp_left, Category.assoc]

end GlobalTheory.Diag

namespace GlobalTheory

open Diag

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun X _ _ _ => ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, fun _ _ => id_ne_one S, fun _ hn => have hn := Nat.one_le_iff_ne_zero.1 hn ⟨isFinite_mulN S X hn, flat_mulN S X hn, surjective_m …`.
-/
theorem splitTorus_properties (S : Scheme.{0}) :
    (∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X],
      IsAffineHom (splitTorus S X).hom ∧ LocallyOfFinitePresentation (splitTorus S X).hom ∧
      QuasiCompact (splitTorus S X).hom ∧ QuasiSeparated (splitTorus S X).hom ∧
      SmoothOfRelativeDimension (Module.finrank ℤ X) (splitTorus S X).hom ∧
      Surjective (splitTorus S X).hom ∧ GeometricallyIntegral (splitTorus S X).hom ∧
      GeometricallyConnected (splitTorus S X).hom ∧ IsSemiAbelian (splitTorus S X) ∧
      (Nonempty S → Nontrivial X → 𝟙 (splitTorus S X) ≠ 1) ∧
      ∀ n : ℕ, 1 ≤ n → IsFinite (mulN (splitTorus S X) n).left ∧
        Flat (mulN (splitTorus S X) n).left ∧ Surjective (mulN (splitTorus S X) n).left ∧
        LocallyOfFinitePresentation (mulN (splitTorus S X) n).left ∧
        ∀ y, (mulN (splitTorus S X) n).left.finrank y = n ^ Module.finrank ℤ X) ∧
    (∀ (S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X],
      IsMonHom (baseChangeIso f X : (Over.pullback f).obj (splitTorus S X) ≅ splitTorus S' X).hom ∧
      ∀ (Y : Type) [AddCommGroup Y] (u : Y →+ X),
        (Over.pullback f).map (diagMap S u) ≫ (baseChangeIso f Y).hom =
          (baseChangeIso f X).hom ≫ diagMap S' u) ∧
    (∀ (X : Type) [AddCommGroup X] [Finite X],
      IsFinite (splitTorus S X).hom ∧ Flat (splitTorus S X).hom ∧
      LocallyOfFinitePresentation (splitTorus S X).hom ∧
      (∀ s, (splitTorus S X).hom.finrank s = Nat.card X) ∧
      (IsUnit (Nat.card X : Γ(S, ⊤)) → Etale (splitTorus S X).hom)) ∧
    (∀ (X Y : Type) [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X),
      IsMonHom (diagMap S u : splitTorus S X ⟶ splitTorus S Y) ∧
      (∀ y, (diagMap S u).left.appTop.hom (chi Y y) = chi X (u y)) ∧
      (∀ v : Y →+ X, diagMap S (u + v) = diagMap S u * diagMap S v) ∧
      (∀ (Z : Type) [AddCommGroup Z] (v : Z →+ Y), diagMap S (u.comp v) = diagMap S u ≫ diagMap S v) ∧
      IsPullback (diagMap S (QuotientAddGroup.mk' u.range)) (toUnit _) (diagMap S u)
        (η : 𝟙_ (Over S) ⟶ splitTorus S Y) ∧
      (Function.Surjective u → IsClosedImmersion (diagMap S u).left) ∧
      (Function.Injective u → Flat (diagMap S u).left ∧ Surjective (diagMap S u).left) ∧
      (u.range.FiniteIndex → IsFinite (diagMap S u).left) ∧
      (Function.Injective u → u.range.FiniteIndex →
        LocallyOfFinitePresentation (diagMap S u).left ∧
          ∀ y, (diagMap S u).left.finrank y = u.range.index)) ∧
    (∀ (X : Type) [AddCommGroup X] (n : ℕ),
      diagMap S (AddMonoidHom.id X) = 𝟙 (splitTorus S X) ∧
      mulN (splitTorus S X) n = diagMap S (nsmulAddMonoidHom n) ∧
      ∃ e : torsion (splitTorus S X) n ≅ splitTorus S (X ⧸ (nsmulAddMonoidHom n : X →+ X).range),
        e.hom ≫ diagMap S (QuotientAddGroup.mk' _) = torsion.ι (splitTorus S X) n) :=
  ⟨fun X _ _ _ => ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, fun _ _ => id_ne_one S,
      fun _ hn => have hn := Nat.one_le_iff_ne_zero.1 hn
        ⟨isFinite_mulN S X hn, flat_mulN S X hn, surjective_mulN S X hn,
          locallyOfFinitePresentation_mulN S X hn, finrank_mulN S X hn⟩⟩,
    fun _ f _ _ => ⟨inferInstance, fun _ _ u => baseChangeIso_naturality f u⟩,
    fun X _ _ => ⟨inferInstance, inferInstance, inferInstance, finrank_hom S X, etale_hom S X⟩,
    fun _ _ _ _ u => ⟨inferInstance, diagMap_chi S u, diagMap_add S u, fun _ _ v => diagMap_comp S u v,
      isPullback_ker S u, isClosedImmersion_diagMap S, fun h => ⟨flat_diagMap S h, surjective_diagMap S h⟩,
      fun _ => isFinite_diagMap S u,
      fun h _ => ⟨locallyOfFinitePresentation_diagMap S h, finrank_diagMap S h⟩⟩,
    fun X _ n => ⟨diagMap_id S, mulN_eq_diagMap S n, torsionIso S X n, torsionIso_hom_diagMap S n⟩⟩

end GlobalTheory
