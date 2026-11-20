import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {X : Over (Sp R)}

/- English proof (translation)
Establish `hb : Function.Bijective T.π` using `⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ by simpa [hT] using (T.ker b).1 hb, T.surj⟩`. Set `e` to `RingEquiv.ofBijective T.π hb`. Set `ρ : T.B₀ →+* T.B` to `e.symm.toRingHom`. Establish `h1 : ρ.comp T.π = RingHom.id _` using `RingHom.ext e.symm_apply_apply`. Establish `h2 : T.π.comp ρ = RingHom.id _` using `RingHom.ext e.apply_symm_apply`.

Establish `k1 : spMap ρ ≫ spMap T.π = 𝟙 _` using `by rw [← Cris.spMap_comp, h1, Cris.spMap_id]`. Establish `k2 : spMap T.π ≫ spMap ρ = 𝟙 _` using `by rw [← Cris.spMap_comp, h2, Cris.spMap_id]`. Establish `hw : (spMap ρ ≫ T.x) ≫ X.hom = spMap (algebraMap R T.B)`. Establish `: T.x ≫ X.hom = spMap (T.π.comp (algebraMap R T.B))` using `(congrArg (T.x ≫ ·) (Category.comp_id X.hom)).symm.trans T.w`. Rewrite using `[Category.assoc, this, Cris.spMap_comp, ← Category.assoc, k1, Category.id_comp]`.

Use `⟨Over.homMk (spMap ρ ≫ T.x) hw, ?_, fun y hy ↦ Over.OverMorphism.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `spMap T.π ≫ spMap ρ ≫ T.x = T.x`. Rewrite using `[← Category.assoc, k2, Category.id_comp]`. Express the relevant statement in the definitionally equal form `y.left = spMap ρ ≫ T.x`. Rewrite using `[← hy, ← Category.assoc, k1]`.

Conclude with `(Category.id_comp _).symm`.
-/
theorem existsUnique_pt_of_triv (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) :
    ∃! y : Pt X T.B, spMap T.π ≫ y.left = T.x := by
  have hb : Function.Bijective T.π :=
    ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ by simpa [hT] using (T.ker b).1 hb, T.surj⟩
  let e := RingEquiv.ofBijective T.π hb
  let ρ : T.B₀ →+* T.B := e.symm.toRingHom
  have h1 : ρ.comp T.π = RingHom.id _ := RingHom.ext e.symm_apply_apply
  have h2 : T.π.comp ρ = RingHom.id _ := RingHom.ext e.apply_symm_apply
  have k1 : spMap ρ ≫ spMap T.π = 𝟙 _ := by rw [← Cris.spMap_comp, h1, Cris.spMap_id]
  have k2 : spMap T.π ≫ spMap ρ = 𝟙 _ := by rw [← Cris.spMap_comp, h2, Cris.spMap_id]
  have hw : (spMap ρ ≫ T.x) ≫ X.hom = spMap (algebraMap R T.B) := by
    have : T.x ≫ X.hom = spMap (T.π.comp (algebraMap R T.B)) :=
      (congrArg (T.x ≫ ·) (Category.comp_id X.hom)).symm.trans T.w
    rw [Category.assoc, this, Cris.spMap_comp, ← Category.assoc, k1, Category.id_comp]
  refine ⟨Over.homMk (spMap ρ ≫ T.x) hw, ?_, fun y hy ↦ Over.OverMorphism.ext ?_⟩
  · change spMap T.π ≫ spMap ρ ≫ T.x = T.x
    rw [← Category.assoc, k2, Category.id_comp]
  · change y.left = spMap ρ ≫ T.x
    rw [← hy, ← Category.assoc, k1]
    exact (Category.id_comp _).symm

def liftHom (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (y : Pt X T.B) (h : spMap T.π ≫ y.left = T.x) : trivAt y ⟶ T :=
  Thick.trivHom (AlgHom.id R T.B) h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hc`. Take `⟨g, hg⟩` from `H1.mk_eq_zero.1 hc`. Use `⟨fun D _ _ x ↦ g ⟨trivAt x, rfl⟩, fun D _ _ D' _ _ φ x _ ↦ ?_⟩` and prove the remaining obligations. Conclude with `(congrFun (congrFun (congrFun hg ⟨trivAt x, rfl⟩) ⟨trivAt (spOver φ ≫ x), rfl⟩) ⟨trivMap φ x⟩).symm`.

Introduce and unpack `⟨k, hk⟩ choose y hy hu using existsUnique_pt_of_triv (R := R) (X := X)`. Use `H1.mk_eq_zero.2 ⟨fun T ↦ (k T.obj.B (y T.obj T.property) + ev f (liftHom T.obj _ (hy T.obj T.property)) : T.obj.B), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `⟨T, hT⟩ ⟨T', hT'⟩ ⟨φ⟩`. Establish `h' : spMap T'.π ≫ (spOver φ.φ ≫ y T hT).left = T'.x`. Express the relevant statement in the definitionally equal form `spMap T'.π ≫ spMap (φ.φ : T.B →+* T'.B) ≫ (y T hT).left = T'.x`.

Rewrite using `[← φ.pt, ← hy T hT, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]`. Use `congr 2`. Conclude with `RingHom.ext fun b ↦ (φ.comm b).symm`. Establish `key : ∀ (z : Pt X T'.B) (hz : spMap T'.π ≫ z.left = T'.x), spOver φ.φ ≫ y T hT = z → k T'.B z + ev f (liftHom T' z hz) - φ.φ (k T.B (y T hT) + ev f (liftHom T _ (hy T hT))) = ev f φ`. Introduce and unpack `_ hz rfl`.

Establish `e1` using `ev_sq f (trivMap φ.φ (y T hT)) (liftHom T' _ hz) (liftHom T _ (hy T hT)) φ fun _ ↦ rfl`. Establish `e2` using `hk T.B T'.B φ.φ (y T hT) (sm_whole _)`. Express the relevant statement in the definitionally equal form `fv f T.B T'.B φ.φ (y T hT) + _ = _ at e1`. Rewrite using `[map_add]`. Take the linear combination `e1 - e2`.

Conclude with `key _ (hy T' hT') (hu T' hT' _ h')`.
-/
theorem mem_hodgeFiltration_iff_pointwiseCoboundary (R : Type) [CommRing R] (X : Over (Sp R)) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) :
    CatCoh.H1.mk _ f ∈ F1 (X.hom ≫ 𝟙 _) ↔ ∃ k : Fn0 X, IsCob (whole X) (fv f) k := by
  constructor
  · intro hc
    obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hc
    refine ⟨fun D _ _ x ↦ g ⟨trivAt x, rfl⟩, fun D _ _ D' _ _ φ x _ ↦ ?_⟩
    exact (congrFun (congrFun (congrFun hg ⟨trivAt x, rfl⟩) ⟨trivAt (spOver φ ≫ x), rfl⟩) ⟨trivMap φ x⟩).symm
  · rintro ⟨k, hk⟩
    choose y hy hu using existsUnique_pt_of_triv (R := R) (X := X)
    refine H1.mk_eq_zero.2 ⟨fun T ↦ (k T.obj.B (y T.obj T.property) +
      ev f (liftHom T.obj _ (hy T.obj T.property)) : T.obj.B), ?_⟩
    funext ⟨T, hT⟩ ⟨T', hT'⟩ ⟨φ⟩
    have h' : spMap T'.π ≫ (spOver φ.φ ≫ y T hT).left = T'.x := by
      change spMap T'.π ≫ spMap (φ.φ : T.B →+* T'.B) ≫ (y T hT).left = T'.x
      rw [← φ.pt, ← hy T hT, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
      congr 2
      exact RingHom.ext fun b ↦ (φ.comm b).symm
    have key : ∀ (z : Pt X T'.B) (hz : spMap T'.π ≫ z.left = T'.x), spOver φ.φ ≫ y T hT = z →
        k T'.B z + ev f (liftHom T' z hz) - φ.φ (k T.B (y T hT) + ev f (liftHom T _ (hy T hT))) = ev f φ := by
      rintro _ hz rfl
      have e1 := ev_sq f (trivMap φ.φ (y T hT)) (liftHom T' _ hz) (liftHom T _ (hy T hT)) φ fun _ ↦ rfl
      have e2 := hk T.B T'.B φ.φ (y T hT) (sm_whole _)
      change fv f T.B T'.B φ.φ (y T hT) + _ = _ at e1
      rw [map_add]
      linear_combination e1 - e2
    exact key _ (hy T' hT') (hu T' hT' _ h')

end GlobalTheory.PtExt
