import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.LieFun

open GlobalTheory.CompanionTheory.Ar.LieTangent

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
  {E : Type} [AddCommGroup E] [Module Ω E]

def Stalk (M : LieModel G ξ E) (p : Cpt ξ) : Type := M.lat p

instance (M : LieModel G ξ E) (p : Cpt ξ) : AddCommGroup (Stalk M p) :=
  inferInstanceAs (AddCommGroup (M.lat p))

instance Stalk.module (M : LieModel G ξ E) (p : Cpt ξ) : Module (X.presheaf.stalk p.1) (Stalk M p) :=
  Module.compHom (M.lat p) (genMap ξ p).rangeRestrict

def Stalk.val {M : LieModel G ξ E} {p : Cpt ξ} (e : Stalk M p) : E := Subtype.val (p := (· ∈ M.lat p)) e

/- English proof (translation)
The claim follows from `Subtype.property e`.
-/
theorem Stalk.mem {M : LieModel G ξ E} {p : Cpt ξ} (e : Stalk M p) : e.val ∈ M.lat p := Subtype.property e

/- English proof (translation)
The claim follows from `Subtype.ext h`.
-/
theorem Stalk.ext {M : LieModel G ξ E} {p : Cpt ξ} {e e' : Stalk M p} (h : e.val = e'.val) : e = e' :=
  Subtype.ext h

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem Stalk.val_add {M : LieModel G ξ E} {p : Cpt ξ} (e e' : Stalk M p) :
    (e + e').val = e.val + e'.val := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem Stalk.val_smul {M : LieModel G ξ E} {p : Cpt ξ} (s : X.presheaf.stalk p.1) (e : Stalk M p) :
    (s • e).val = genMap ξ p s • e.val := rfl

def Stalk.tan {M : LieModel G ξ E} {p : Cpt ξ} (e : Stalk M p) :
    epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G :=
  ((M.mem_lat_iff p e.val).1 e.mem).choose

/- English proof (translation)
The claim follows from `((M.mem_lat_iff p e.val).1 e.mem).choose_spec`.
-/
theorem Stalk.tan_spec {M : LieModel G ξ E} {p : Cpt ξ} (e : Stalk M p) : M.Extends p e.val e.tan :=
  ((M.mem_lat_iff p e.val).1 e.mem).choose_spec

def stalkLie (hξ : IsCptGen ξ) (M : LieModel G ξ E) (p : Cpt ξ) :
    LieModel (R := X.presheaf.stalk p.1) G (X.fromSpecStalk p.1) (Stalk M p) where
  pt e := e.tan
  tan e := e.tan_spec.1
  inj e e' h := by
    refine Stalk.ext (M.inj ?_)
    have a := ((M.extends_iff _ _ _).1 e.tan_spec).2
    have b := ((M.extends_iff _ _ _).1 e'.tan_spec).2
    rw [a, b]
    exact congrArg _ h
  onto v hv := by
    obtain ⟨e, he⟩ := M.onto _ (isTanAt_base (genMap ξ p) (spec_genMap ξ p) hv)
    have hx : M.Extends p e v := (M.extends_iff _ _ _).2 ⟨hv, he⟩
    let e' : Stalk M p := ⟨e, (M.mem_lat_iff _ _).2 ⟨v, hx⟩⟩
    exact ⟨e', e'.tan_spec.unique (hξ.inj p) hx⟩
  add e e' := (e + e').tan_spec.unique (hξ.inj p) (e.tan_spec.add e'.tan_spec)
  smul c e := congrArg (fun q => q.left) ((c • e).tan_spec.unique (hξ.inj p) (e.tan_spec.smul c))

def castLie {R : Type} [CommRing R] {x y : Sp R ⟶ X} (h : x = y) {F : Type} [AddCommGroup F] [Module R F]
    (M : LieModel G x F) : LieModel G y F := h ▸ M

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem castLie_left {R : Type} [CommRing R] {x y : Sp R ⟶ X} (h : x = y) {F : Type} [AddCommGroup F]
    [Module R F] (M : LieModel G x F) (e : F) : ((castLie h M).pt e).left = (M.pt e).left := by
  subst h
  rfl

end GlobalTheory.CompanionTheory.Ar.RootHt.LieFun

namespace GlobalTheory.CompanionTheory.Ar.RootHt

open GlobalTheory.CompanionTheory.Ar.RootHt.LieFun GlobalTheory.CompanionTheory.Ar.LieTangent

/- English proof (translation)
Introduce `X G _ _ _ Ω _ ξ Li _ _ M R _ _ z h ER _ _ MR f hξ hf`. Take `⟨ev, hev, hlin, -⟩` from `GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ Li M R z h ER MR hξ inferInstance`. Set `ψ : X.presheaf.stalk (centre z) →+* R` to `(Scheme.stalkClosedPointTo z).hom`. Use `letI : Algebra (X.presheaf.stalk (centre z)) R := ψ.toAlgebra`. Use `letI : Module (X.presheaf.stalk (centre z)) ER := Module.compHom ER ψ`.

Use `haveI : IsScalarTower (X.presheaf.stalk (centre z)) R ER := ⟨fun s r x => by`. Express the relevant statement in the definitionally equal form `(ψ s * r) • x = ψ s • r • x`. Rewrite using `[mul_smul]⟩`. Use `letI : Module (X.presheaf.stalk (centre z)) (Stalk M ⟨centre z, h⟩) := Stalk.module M ⟨centre z, h⟩`. Establish `hgi : Function.Injective (genMap ξ ⟨centre z, h⟩)` using `hξ.inj ⟨centre z, h⟩`.

Set `j : Stalk M ⟨centre z, h⟩ →ₗ[X.presheaf.stalk (centre z)] ER` to `{ toFun := fun e => ev ⟨e.val, e.mem⟩ map_add' := fun e e' => ev.map_add ⟨e.val, e.mem⟩ ⟨e'.val, e'.mem⟩ map_smul' := fun s e => hlin ⟨genMap ξ ⟨centre z, h⟩ s, s, rfl⟩ (ψ s) ⟨e.val, e.mem⟩ ⟨h, s, rfl, rfl⟩ }`. Establish `hbc : IsBaseChange R j`. Use `GlobalTheory.T.lie_model_isBaseChange X G (X.presheaf.stalk (centre z)) R (X.fromSpecStalk (centre z)) (Stalk M ⟨centre z, h⟩) ER (stalkLie hξ M ⟨centre z, h⟩) (castLie (spec_centre z).symm MR) j fun e => ?_` and prove the remaining obligations. Take `⟨h', v, hv, hw⟩` from `(hev e.val (ev ⟨e.val, e.mem⟩)).2 ⟨e.mem, rfl⟩`. Establish `hvv : v = e.tan` using `hv.unique (hξ.inj _) e.tan_spec`.

Substitute `hvv` using the available equality. Use `show ((castLie (spec_centre z).symm MR).pt (j e)).left ≫ 𝟙 G.left = _`. Rewrite using `[Category.comp_id, castLie_left]`. Conclude with `hw`. Establish `hs : ∀ e : Stalk M ⟨centre z, h⟩, ∃ s, genMap ξ ⟨centre z, h⟩ s = f e.val` using `fun e => hf e.val e.mem`.

Use `choose σ hσ using hs`. Set `f' : Stalk M ⟨centre z, h⟩ →ₗ[X.presheaf.stalk (centre z)] R` to `{ toFun := fun e => ψ (σ e) map_add' := fun e e' => by`. Establish `: σ (e + e') = σ e + σ e'` using `hgi (by simp [hσ])`. Rewrite using `[this, map_add]`. Use the proof step `map_smul' := fun s e => by`.

Establish `: σ (s • e) = s * σ e` using `hgi (by`. Rewrite using `[hσ, map_mul, hσ]`. Use `show f (genMap ξ ⟨centre z, h⟩ s • e.val) = _`. Rewrite using `[map_smul, smul_eq_mul])`. Rewrite using `[this, map_mul]`.

Use `rfl }`. Use `⟨hbc.lift f', fun e x u hV hU => ?_⟩` and prove the remaining obligations. Take `⟨he, rfl⟩` from `(hev e x).1 hV`. Take `⟨h2, s, hs1, hs2⟩` from `hU`. Set `e' : Stalk M ⟨centre z, h⟩` to `⟨e, he⟩`.

Establish `h3 : hbc.lift f' (j e') = f' e'` using `hbc.lift_eq f' e'`. Establish `h4 : σ e' = s` using `hgi ((hσ e').trans hs1.symm)`. Establish `h5 : f' e' = ψ (σ e')` using `rfl`. Rewrite `h5` using `[h4]`. Conclude with `(h3.trans h5).trans hs2`.
-/
theorem exists_lieFunctional : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (R : Type) [CommRing R] [IsLocalRing R]
    (z : Sp R ⟶ X) (h : genPt ξ ⤳ centre z) (ER : Type) [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER)
    (f : Module.Dual Ω Li), IsCptGen ξ → (∀ e ∈ M.lat ⟨centre z, h⟩, f e ∈ regAt ξ ⟨centre z, h⟩) →
    ∃ g : ER →ₗ[R] R, ∀ (e : Li) (x : ER) (u : R), M.ValAt z e (MR.pt x) → ValAt ξ z (f e) u → g x = u := by
  intro X G _ _ _ Ω _ ξ Li _ _ M R _ _ z h ER _ _ MR f hξ hf
  obtain ⟨ev, hev, hlin, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ Li M R z h ER MR hξ inferInstance
  let ψ : X.presheaf.stalk (centre z) →+* R := (Scheme.stalkClosedPointTo z).hom
  letI : Algebra (X.presheaf.stalk (centre z)) R := ψ.toAlgebra
  letI : Module (X.presheaf.stalk (centre z)) ER := Module.compHom ER ψ
  haveI : IsScalarTower (X.presheaf.stalk (centre z)) R ER :=
    ⟨fun s r x => by
      change (ψ s * r) • x = ψ s • r • x
      rw [mul_smul]⟩
  letI : Module (X.presheaf.stalk (centre z)) (Stalk M ⟨centre z, h⟩) := Stalk.module M ⟨centre z, h⟩
  have hgi : Function.Injective (genMap ξ ⟨centre z, h⟩) := hξ.inj ⟨centre z, h⟩

  let j : Stalk M ⟨centre z, h⟩ →ₗ[X.presheaf.stalk (centre z)] ER :=
    { toFun := fun e => ev ⟨e.val, e.mem⟩
      map_add' := fun e e' => ev.map_add ⟨e.val, e.mem⟩ ⟨e'.val, e'.mem⟩
      map_smul' := fun s e => hlin ⟨genMap ξ ⟨centre z, h⟩ s, s, rfl⟩ (ψ s) ⟨e.val, e.mem⟩ ⟨h, s, rfl, rfl⟩ }
  have hbc : IsBaseChange R j := by
    refine GlobalTheory.T.lie_model_isBaseChange X G (X.presheaf.stalk (centre z)) R (X.fromSpecStalk (centre z)) (Stalk M ⟨centre z, h⟩) ER
      (stalkLie hξ M ⟨centre z, h⟩) (castLie (spec_centre z).symm MR) j fun e => ?_
    obtain ⟨h', v, hv, hw⟩ := (hev e.val (ev ⟨e.val, e.mem⟩)).2 ⟨e.mem, rfl⟩
    have hvv : v = e.tan := hv.unique (hξ.inj _) e.tan_spec
    subst hvv
    show ((castLie (spec_centre z).symm MR).pt (j e)).left ≫ 𝟙 G.left = _
    rw [Category.comp_id, castLie_left]
    exact hw
  have hs : ∀ e : Stalk M ⟨centre z, h⟩, ∃ s, genMap ξ ⟨centre z, h⟩ s = f e.val := fun e => hf e.val e.mem
  choose σ hσ using hs
  let f' : Stalk M ⟨centre z, h⟩ →ₗ[X.presheaf.stalk (centre z)] R :=
    { toFun := fun e => ψ (σ e)
      map_add' := fun e e' => by
        have : σ (e + e') = σ e + σ e' := hgi (by simp [hσ])
        rw [this, map_add]
      map_smul' := fun s e => by
        have : σ (s • e) = s * σ e := hgi (by
          rw [hσ, map_mul, hσ]
          show f (genMap ξ ⟨centre z, h⟩ s • e.val) = _
          rw [map_smul, smul_eq_mul])
        rw [this, map_mul]
        rfl }
  refine ⟨hbc.lift f', fun e x u hV hU => ?_⟩
  obtain ⟨he, rfl⟩ := (hev e x).1 hV
  obtain ⟨h2, s, hs1, hs2⟩ := hU
  let e' : Stalk M ⟨centre z, h⟩ := ⟨e, he⟩
  have h3 : hbc.lift f' (j e') = f' e' := hbc.lift_eq f' e'
  have h4 : σ e' = s := hgi ((hσ e').trans hs1.symm)
  have h5 : f' e' = ψ (σ e') := rfl
  rw [h4] at h5
  exact (h3.trans h5).trans hs2

end GlobalTheory.CompanionTheory.Ar.RootHt
