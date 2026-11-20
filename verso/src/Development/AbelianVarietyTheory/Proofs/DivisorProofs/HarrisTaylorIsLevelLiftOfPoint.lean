import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudePrimeToPPullbackSquareStatement

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Introduce `p _ D R _ b N N' hd hc S S' s s' o o' f om T g lv hT hlv`. Take `⟨T, ⟨⟨⟩⟩, h⟩` from `T`. Express the relevant statement in the definitionally equal form `T ⟶ S' at g`. Use `replace hT : (g ≫ f : T ⟶ S) = h := hT`. Substitute `hT` using the available equality.

Take `⟨φ, hφ⟩ : ∃ φ : o'.A.left ⟶ o.A.left, φ = om.φ` from `⟨om.φ, rfl⟩`. Establish `hlv' : ∀ a, (lv a).left = g ≫ (o'.eta a).left ≫ φ` using `fun a => by rw [hφ]; exact hlv a`. Establish `cart : IsGrpPullback o'.A o.A f φ` using `by rw [hφ]; exact om.cart`. Establish `sq : IsSquare φ om.φ₂` using `by rw [hφ]; exact om.sq`. Establish `ha : ∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left` using `fun c => by rw [hφ]; exact om.act c`.

Establish `he : ∀ x, (o'.eta ((N' / N) • x)).left ≫ φ = f ≫ (o.eta x).left` using `fun x => by rw [hφ]; exact om.eta x`. Set `T' : Over S'` to `Over.mk g`. Set `q : D.La → (T' ⟶ o'.A)` to `fun a => toUnit T' ≫ o'.eta a`. Establish `hq : ∀ a, (q a).left = g ≫ (o'.eta a).left` using `fun a => by`. Simplify using `only [q, Over.comp_left, Over.toUnit_left]`.

Both sides reduce to the same expression. Establish `key : ∀ a, (lv a).left = (q a).left ≫ φ` using `fun a => by rw [hlv', hq, Category.assoc]`. Establish `mulx : ∀ x y : D.La, (lv x * lv y).left = (q x * q y).left ≫ φ` using `fun x y => cart.2 T' (q x) (q y) (lv x) (lv y) (key x) (key y)`. Use `⟨fun x y => ?_, fun x => ?_, fun c x => ?_, fun x => ?_, fun k _ _ x => ?_⟩` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[mulx, key]`. Use `congr 1`. Use `show (toUnit T' ≫ o'.eta (x + y)).left = (toUnit T' ≫ o'.eta x * toUnit T' ≫ o'.eta y).left`. Rewrite using `[o'.eta_add, MonObj.comp_mul]`. Establish `h1 : q (N' • x) = 1` using `by show toUnit T' ≫ o'.eta (N' • x) = 1`.

Rewrite using `[o'.eta_ker, MonObj.comp_one]`. Establish `hzz : lv (N' • x) * lv (N' • x) = lv (N' • x) * 1`. Rewrite using `[_root_.mul_one]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[mulx, key, h1, _root_.mul_one]`.

Conclude with `mul_left_cancel hzz`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, hlv', hlv', o'.eta_lin, Over.comp_left]`. Simplify using `only [Category.assoc, ha]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[hlv', he, Over.comp_left, Over.toUnit_left]`. Conclude with `(Category.assoc _ _ _).symm`. Take `⟨I', hI'⟩` from `o'.geom k (x ≫ g) (Spec.preimage ((x ≫ g) ≫ s')).hom (Spec.map_preimage _).symm`. Establish `h3` using `(GlobalTheory.T.tateSimilitude_prime_to_p_pullback_square p D R b N N' S S' s s' o o' f φ om.φ₂ cart sq ha om.pol k (x ≫ g)).1 I'`. Rewrite `h3` using `[Category.assoc]`.

Take `⟨I, hI⟩` from `h3`. Use `⟨I, fun y => ?_⟩` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, hI, ← hI' y, Over.comp_left, Over.toUnit_left]`. Express the relevant statement in the definitionally equal form `x ≫ (lv y).left = _`.

Rewrite using `[hlv']`. Simplify using `only [Over.mk_hom, Category.assoc]`.
-/
theorem isLift_of_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N' s') (f : S' ⟶ S) (om : ObjMap (o'.forget N hd hc) o f) (T : Over S) (g : T.left ⟶ S') (lv : D.La → (T ⟶ o.A)), g ≫ f = T.hom → (∀ a, (lv a).left = g ≫ (o'.eta a).left ≫ om.φ) → IsLift o N' T lv := by
  intro p _ D R _ b N N' hd hc S S' s s' o o' f om T g lv hT hlv
  obtain ⟨T, ⟨⟨⟩⟩, h⟩ := T
  change T ⟶ S' at g
  replace hT : (g ≫ f : T ⟶ S) = h := hT
  subst hT
  obtain ⟨φ, hφ⟩ : ∃ φ : o'.A.left ⟶ o.A.left, φ = om.φ := ⟨om.φ, rfl⟩
  have hlv' : ∀ a, (lv a).left = g ≫ (o'.eta a).left ≫ φ := fun a => by rw [hφ]; exact hlv a
  have cart : IsGrpPullback o'.A o.A f φ := by rw [hφ]; exact om.cart
  have sq : IsSquare φ om.φ₂ := by rw [hφ]; exact om.sq
  have ha : ∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left := fun c => by rw [hφ]; exact om.act c
  have he : ∀ x, (o'.eta ((N' / N) • x)).left ≫ φ = f ≫ (o.eta x).left := fun x => by rw [hφ]; exact om.eta x
  let T' : Over S' := Over.mk g
  let q : D.La → (T' ⟶ o'.A) := fun a => toUnit T' ≫ o'.eta a
  have hq : ∀ a, (q a).left = g ≫ (o'.eta a).left := fun a => by
    simp only [q, Over.comp_left, Over.toUnit_left]
    rfl
  have key : ∀ a, (lv a).left = (q a).left ≫ φ := fun a => by rw [hlv', hq, Category.assoc]
  have mulx : ∀ x y : D.La, (lv x * lv y).left = (q x * q y).left ≫ φ := fun x y =>
    cart.2 T' (q x) (q y) (lv x) (lv y) (key x) (key y)
  refine ⟨fun x y => ?_, fun x => ?_, fun c x => ?_, fun x => ?_, fun k _ _ x => ?_⟩
  · apply Over.OverMorphism.ext
    rw [mulx, key]
    congr 1
    show (toUnit T' ≫ o'.eta (x + y)).left = (toUnit T' ≫ o'.eta x * toUnit T' ≫ o'.eta y).left
    rw [o'.eta_add, MonObj.comp_mul]
  · have h1 : q (N' • x) = 1 := by
      show toUnit T' ≫ o'.eta (N' • x) = 1
      rw [o'.eta_ker, MonObj.comp_one]
    have hzz : lv (N' • x) * lv (N' • x) = lv (N' • x) * 1 := by
      rw [_root_.mul_one]
      apply Over.OverMorphism.ext
      rw [mulx, key, h1, _root_.mul_one]
    exact mul_left_cancel hzz
  · apply Over.OverMorphism.ext
    rw [Over.comp_left, hlv', hlv', o'.eta_lin, Over.comp_left]
    simp only [Category.assoc, ha]
  · apply Over.OverMorphism.ext
    rw [hlv', he, Over.comp_left, Over.toUnit_left]
    exact (Category.assoc _ _ _).symm
  · obtain ⟨I', hI'⟩ := o'.geom k (x ≫ g) (Spec.preimage ((x ≫ g) ≫ s')).hom (Spec.map_preimage _).symm
    have h3 := (GlobalTheory.T.tateSimilitude_prime_to_p_pullback_square p D R b N N' S S' s s' o o' f φ om.φ₂ cart sq ha om.pol k (x ≫ g)).1 I'
    rw [Category.assoc] at h3
    obtain ⟨I, hI⟩ := h3
    refine ⟨I, fun y => ?_⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hI, ← hI' y, Over.comp_left, Over.toUnit_left]
    change x ≫ (lv y).left = _
    rw [hlv']
    simp only [Over.mk_hom, Category.assoc]

end GlobalTheory.UPel.HT
