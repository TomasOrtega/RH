import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S}

def secPush (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) : Over.mk (T.hom ≫ f) ⟶ o.A :=
  Over.homMk (u.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]; rfl)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem secPush_left (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) :
    (secPush m T u).left = u.left ≫ m.φ := rfl

/- English proof (translation)
Establish `h'` using `congrArg CommaMorphism.left h`. Conclude with `Over.OverMorphism.ext (m.cart.1.hom_ext h' (by rw [Over.w, Over.w]))`.
-/
theorem secPush_inj (m : ObjMap o' o f) (T : Over S') {u v : T ⟶ o'.A}
    (h : secPush m T u = secPush m T v) : u = v := by
  have h' := congrArg CommaMorphism.left h
  exact Over.OverMorphism.ext (m.cart.1.hom_ext h' (by rw [Over.w, Over.w]))

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[secPush_left]`. Conclude with `(m.cart.2 T u v (secPush m T u) (secPush m T v) rfl rfl).symm`.
-/
theorem secPush_mul (m : ObjMap o' o f) (T : Over S') (u v : T ⟶ o'.A) :
    secPush m T (u * v) = secPush m T u * secPush m T v := by
  apply Over.OverMorphism.ext
  rw [secPush_left]
  exact (m.cart.2 T u v (secPush m T u) (secPush m T v) rfl rfl).symm

/- English proof (translation)
Establish `h` using `secPush_mul m T 1 1`. Rewrite `h` using `[_root_.mul_one]`. Conclude with `(_root_.mul_eq_left.mp h.symm)`.
-/
theorem secPush_one (m : ObjMap o' o f) (T : Over S') :
    secPush m T 1 = 1 := by
  have h := secPush_mul m T 1 1
  rw [_root_.mul_one] at h
  exact (_root_.mul_eq_left.mp h.symm)

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `only [secPush_left, Over.comp_left, Category.assoc, m.act]`.
-/
theorem secPush_act (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) (c : D.O) :
    secPush m T (u ≫ o'.act.act c) = secPush m T u ≫ o.act.act c := by
  apply Over.OverMorphism.ext
  simp only [secPush_left, Over.comp_left, Category.assoc, m.act]

/- English proof (translation)
Introduce `p _ D R _ b N S S' s s' o o' f m w0 r lv hlv`. Establish `hu : ∀ {X : Scheme.{0}} (T : Over X), (toUnit T).left = T.hom` using `fun T => (Category.comp_id _).symm.trans (Over.w (toUnit T))`. Establish `wα : ∀ y, (f ≫ (lv y).left) ≫ o.A.hom = 𝟙 S' ≫ f` using `fun y => by`. Rewrite using `[Category.assoc, Over.w]`. Simplify using the standard rewrite rules.

Set `lv' : D.La → (𝟙_ (Over S') ⟶ o'.A)` to `fun y => Over.homMk (m.cart.1.lift (f ≫ (lv y).left) (𝟙 S') (wα y)) (m.cart.1.lift_snd _ _ _)`. Establish `hα : ∀ y, (lv' y).left ≫ m.φ = f ≫ (lv y).left` using `fun y => m.cart.1.lift_fst _ _ _`. Establish `hP1 : ∀ y, secPush m (𝟙_ (Over S')) (lv' y) = toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f)) ≫ lv y` using `fun y => by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[secPush_left, hα, Over.comp_left, hu]`.

Simplify using the standard rewrite rules. Establish `hP : ∀ (T : Over S') y, secPush m T (toUnit T ≫ lv' y) = toUnit (Over.mk (T.hom ≫ f)) ≫ lv y` using `fun T y => by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[secPush_left, Over.comp_left, Category.assoc, hα, Over.comp_left, hu, hu]`. Simplify using the standard rewrite rules.

Use `⟨lv', ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x' => ?_⟩, hα⟩` and prove the remaining obligations. Apply `secPush_inj m` to reduce the goal to its premises. Rewrite using `[secPush_mul, hP1, hP1, hP1, hlv.1, MonObj.comp_mul]`. Apply `secPush_inj m` to reduce the goal to its premises. Rewrite using `[secPush_act, hP1, hP1, hlv.2.1, Category.assoc]`.

Apply `secPush_inj m` to reduce the goal to its premises. Rewrite using `[hP1, secPush_one, hlv.2.2.1 x hx, MonObj.comp_one]`. Take `⟨hinj, hsurj⟩` from `hlv.2.2.2 k (x' ≫ f)`. Use `⟨fun y hy => hinj y ?_, fun g hg => ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (secPush m (Over.mk x')) hy`.

Rewrite `h` using `[hP, secPush_one]`. Conclude with `h`. Take `⟨y, hy⟩` from `hsurj (secPush m (Over.mk x') g) (fun c hc => by`. Rewrite using `[← secPush_act, hg c hc, secPush_one])`. Use `⟨y, secPush_inj m _ ?_⟩` and prove the remaining obligations.

Rewrite using `[hP]`. Conclude with `hy`.
-/
theorem isEtLev_exists_pull : ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S} (m : ObjMap o' o f) {w0 : Ideal (𝓞 D.F)} {r : ℕ} {lv : D.La → (𝟙_ (Over S) ⟶ o.A)}, IsEtLev o w0 r lv → ∃ lv' : D.La → (𝟙_ (Over S') ⟶ o'.A), IsEtLev o' w0 r lv' ∧ ∀ y, (lv' y).left ≫ m.φ = f ≫ (lv y).left := by
  intro p _ D R _ b N S S' s s' o o' f m w0 r lv hlv
  have hu : ∀ {X : Scheme.{0}} (T : Over X), (toUnit T).left = T.hom := fun T =>
    (Category.comp_id _).symm.trans (Over.w (toUnit T))
  have wα : ∀ y, (f ≫ (lv y).left) ≫ o.A.hom = 𝟙 S' ≫ f := fun y => by
    rw [Category.assoc, Over.w]; simp
  let lv' : D.La → (𝟙_ (Over S') ⟶ o'.A) := fun y =>
    Over.homMk (m.cart.1.lift (f ≫ (lv y).left) (𝟙 S') (wα y)) (m.cart.1.lift_snd _ _ _)
  have hα : ∀ y, (lv' y).left ≫ m.φ = f ≫ (lv y).left := fun y => m.cart.1.lift_fst _ _ _
  have hP1 : ∀ y, secPush m (𝟙_ (Over S')) (lv' y) =
      toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f)) ≫ lv y := fun y => by
    apply Over.OverMorphism.ext
    rw [secPush_left, hα, Over.comp_left, hu]; simp
  have hP : ∀ (T : Over S') y, secPush m T (toUnit T ≫ lv' y) =
      toUnit (Over.mk (T.hom ≫ f)) ≫ lv y := fun T y => by
    apply Over.OverMorphism.ext
    rw [secPush_left, Over.comp_left, Category.assoc, hα, Over.comp_left, hu, hu]; simp
  refine ⟨lv', ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x' => ?_⟩, hα⟩
  · apply secPush_inj m
    rw [secPush_mul, hP1, hP1, hP1, hlv.1, MonObj.comp_mul]
  · apply secPush_inj m
    rw [secPush_act, hP1, hP1, hlv.2.1, Category.assoc]
  · apply secPush_inj m
    rw [hP1, secPush_one, hlv.2.2.1 x hx, MonObj.comp_one]
  · obtain ⟨hinj, hsurj⟩ := hlv.2.2.2 k (x' ≫ f)
    refine ⟨fun y hy => hinj y ?_, fun g hg => ?_⟩
    · have h := congrArg (secPush m (Over.mk x')) hy
      rw [hP, secPush_one] at h
      exact h
    · obtain ⟨y, hy⟩ := hsurj (secPush m (Over.mk x') g) (fun c hc => by
        rw [← secPush_act, hg c hc, secPush_one])
      refine ⟨y, secPush_inj m _ ?_⟩
      rw [hP]
      exact hy

end GlobalTheory.UPel.HT.EtLev
