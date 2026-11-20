import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LineConst

open Polynomial

variable (k : Type) [Field k]

def scaleHom (R : Type) [CommRing R] [Algebra k R] (u : R) : Polynomial k →+* Polynomial R :=
  Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap k R)) (Polynomial.C u * Polynomial.X)

/- English proof (translation)
Use extensionality with `a`. Simplify using `[scaleHom, Polynomial.algebraMap_apply]`.
-/
theorem scaleHom_algebraMap (R : Type) [CommRing R] [Algebra k R] (u : R) :
    (scaleHom k R u).comp (algebraMap k (Polynomial k)) = algebraMap k (Polynomial R) := by
  ext a
  simp [scaleHom, Polynomial.algebraMap_apply]

def lineOver (R : Type) [CommRing R] [Algebra k R] : Over (Sp k) :=
  Over.mk (spMap (algebraMap k (Polynomial R)))

variable {k}

def scaled (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] (u : R) :
    lineOver k R ⟶ B :=
  Over.homMk (spMap (scaleHom k R u) ≫ f) (by
    change spMap (scaleHom k R u) ≫ f ≫ B.hom = spMap (algebraMap k (Polynomial R))
    rw [hf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, scaleHom_algebraMap])

def famMap (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] (u : R) : Sp (Polynomial R) ⟶ B.left :=
  (scaled B f hf R u * (scaled B f hf R 1)⁻¹).left

end GlobalTheory.LineConst

namespace GlobalTheory.LineConst
open Polynomial

/- English proof (translation)
Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[scaleHom]`. Simplify using `[scaleHom]`.
-/
theorem scaleHom_comp_map {k : Type} [Field k] {R R' : Type} [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R']
    (φ : R →ₐ[k] R') (u : R) :
    (Polynomial.mapRingHom (φ : R →+* R')).comp (scaleHom k R u) = scaleHom k R' (φ u) := by
  apply Polynomial.ringHom_ext
  · intro a; simp [scaleHom]
  · simp [scaleHom]

def lineMap {k : Type} [Field k] {R R' : Type} [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R']
    (φ : R →ₐ[k] R') : lineOver k R' ⟶ lineOver k R :=
  Over.homMk (spMap (Polynomial.mapRingHom (φ : R →+* R'))) (by
    change spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ spMap (algebraMap k (Polynomial R)) =
      spMap (algebraMap k (Polynomial R'))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a; simp [Polynomial.algebraMap_apply])

/- English proof (translation)
Use `ext1`. Express the relevant statement in the definitionally equal form `spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ spMap (scaleHom k R u) ≫ f = spMap (scaleHom k R' (φ u)) ≫ f`. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, scaleHom_comp_map]`.
-/
theorem lineMap_scaled {k : Type} [Field k] (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) {R R' : Type} [CommRing R] [Algebra k R]
    [CommRing R'] [Algebra k R'] (φ : R →ₐ[k] R') (u : R) :
    lineMap φ ≫ scaled B f hf R u = scaled B f hf R' (φ u) := by
  ext1
  change spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ spMap (scaleHom k R u) ≫ f =
    spMap (scaleHom k R' (φ u)) ≫ f
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, scaleHom_comp_map]

/- English proof (translation)
Establish `h` using `congrArg CommaMorphism.left (show lineMap φ ≫ (scaled B f hf R u * (scaled B f hf R 1)⁻¹) = scaled B f hf R' (φ u) * (scaled B f hf R' 1)⁻¹ by`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, lineMap_scaled, lineMap_scaled, map_one])`. Conclude with `h`.
-/
theorem famMap_base {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) {R R' : Type} [CommRing R] [Algebra k R]
    [CommRing R'] [Algebra k R'] (φ : R →ₐ[k] R') (u : R) :
    spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ famMap B f hf R u = famMap B f hf R' (φ u) := by
  have h := congrArg CommaMorphism.left
    (show lineMap φ ≫ (scaled B f hf R u * (scaled B f hf R 1)⁻¹) =
      scaled B f hf R' (φ u) * (scaled B f hf R' 1)⁻¹ by
      rw [MonObj.comp_mul, GrpObj.comp_inv, lineMap_scaled, lineMap_scaled, map_one])
  exact h

/- English proof (translation)
Unfold `famMap`. Rewrite using `[mul_inv_cancel, Hom.one_def, Over.comp_left]`. Use `congr 1`.
-/
theorem famMap_one {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] :
    famMap B f hf R 1 = spMap (algebraMap k (Polynomial R)) ≫ (η[B] : 𝟙_ (Over (Sp k)) ⟶ B).left := by
  unfold famMap
  rw [mul_inv_cancel, Hom.one_def, Over.comp_left]
  congr 1

end GlobalTheory.LineConst

namespace GlobalTheory.LineConst
open Polynomial

def linePt {k : Type} [Field k] (a : k) : 𝟙_ (Over (Sp k)) ⟶ lineOver k k :=
  Over.homMk (spMap (Polynomial.evalRingHom a)) (by
    change spMap (Polynomial.evalRingHom a) ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.evalRingHom a).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id])

/- English proof (translation)
Express the relevant statement in the definitionally equal form `spMap (Polynomial.evalRingHom a) ≫ spMap (scaleHom k k c) ≫ f = _`. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 3`. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `z`.

Simplify using `[scaleHom]`. Simplify using `[scaleHom]`.
-/
theorem linePt_scaled_left {k : Type} [Field k] (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (a c : k) :
    (linePt a ≫ scaled B f hf k c).left = spMap (Polynomial.evalRingHom (c * a)) ≫ f := by
  change spMap (Polynomial.evalRingHom a) ≫ spMap (scaleHom k k c) ≫ f = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  apply Polynomial.ringHom_ext
  · intro z; simp [scaleHom]
  · simp [scaleHom]

/- English proof (translation)
Establish `hpt : ∀ b : k, spMap (Polynomial.evalRingHom b) ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _`. Introduce `b`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Establish `: (Polynomial.evalRingHom b).comp (algebraMap k (Polynomial k)) = RingHom.id k`. Use extensionality with `z`.

Simplify using the standard rewrite rules. Rewrite using `[this, CommRingCat.ofHom_id, Spec.map_id]`. Establish `hleft : spMap (Polynomial.evalRingHom a) ≫ famMap B f hf k c = spMap (Polynomial.evalRingHom 0) ≫ famMap B f hf k c` using `by conv_lhs => rw [h]`. Rewrite using `[← Category.assoc, hpt, Category.id_comp]`. Establish `hq : ∀ b : k, linePt b ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) = (linePt b ≫ scaled B f hf k c) * (linePt b ≫ scaled B f hf k 1)⁻¹`.

Introduce `b`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv]`. Establish `h0 : linePt 0 ≫ scaled B f hf k c = linePt 0 ≫ scaled B f hf k 1` using `by ext1`. Rewrite using `[linePt_scaled_left, linePt_scaled_left, mul_zero, mul_zero]`. Establish `hall : linePt a ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) = linePt 0 ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹)` using `by ext1`.

Conclude with `hleft`. Rewrite `hall` using `[hq, hq, h0, mul_inv_cancel]`. Establish `hall' : linePt a ≫ scaled B f hf k c = linePt a ≫ scaled B f hf k 1` using `mul_inv_eq_one.mp hall`. Establish `h2` using `congrArg CommaMorphism.left hall'`. Establish `e1` using `linePt_scaled_left B f hf a c`.

Establish `e2` using `linePt_scaled_left B f hf a 1`. Rewrite `e2` using `[_root_.one_mul]`. Rewrite using `[← e1, ← e2]`. Conclude with `h2`.
-/
theorem scale_inv_of_famMap {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (c : k)
    (h : famMap B f hf k c = spMap (algebraMap k (Polynomial k)) ≫ spMap (Polynomial.evalRingHom 0) ≫ famMap B f hf k c)
    (a : k) : spMap (Polynomial.evalRingHom (c * a)) ≫ f = spMap (Polynomial.evalRingHom a) ≫ f := by
  have hpt : ∀ b : k, spMap (Polynomial.evalRingHom b) ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _ := by
    intro b
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.evalRingHom b).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  have hleft : spMap (Polynomial.evalRingHom a) ≫ famMap B f hf k c =
      spMap (Polynomial.evalRingHom 0) ≫ famMap B f hf k c := by
    conv_lhs => rw [h]
    rw [← Category.assoc, hpt, Category.id_comp]
  have hq : ∀ b : k, linePt b ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) =
      (linePt b ≫ scaled B f hf k c) * (linePt b ≫ scaled B f hf k 1)⁻¹ := by
    intro b; rw [MonObj.comp_mul, GrpObj.comp_inv]
  have h0 : linePt 0 ≫ scaled B f hf k c = linePt 0 ≫ scaled B f hf k 1 := by
    ext1
    rw [linePt_scaled_left, linePt_scaled_left, mul_zero, mul_zero]
  have hall : linePt a ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) =
      linePt 0 ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) := by
    ext1
    exact hleft
  rw [hq, hq, h0, mul_inv_cancel] at hall
  have hall' : linePt a ≫ scaled B f hf k c = linePt a ≫ scaled B f hf k 1 :=
    mul_inv_eq_one.mp hall
  have h2 := congrArg CommaMorphism.left hall'
  have e1 := linePt_scaled_left B f hf a c
  have e2 := linePt_scaled_left B f hf a 1
  rw [_root_.one_mul] at e2
  rw [← e1, ← e2]
  exact h2

end GlobalTheory.LineConst
