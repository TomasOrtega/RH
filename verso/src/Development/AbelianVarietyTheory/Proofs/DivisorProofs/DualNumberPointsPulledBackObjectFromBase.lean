import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNsmulEqOfEqClosedPointDualNumbers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.EpsPts

variable {S S₀ : Scheme.{0}}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unit_hom (X : Scheme.{0}) : (𝟙_ (Over X)).hom = 𝟙 X := rfl

/- English proof (translation)
Set `P` to `h₂.lift (g ≫ a) g (by rw [Category.assoc, ha, Category.comp_id])`. Use `⟨h₁.lift P (𝟙 S) (by rw [h₂.lift_snd, Category.id_comp]), ?_, h₁.lift_snd _ _ _⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, h₁.lift_fst, h₂.lift_fst]`.
-/
theorem exists_pt {G : Over S} {G₀ A : Over S₀} {g : S ⟶ S₀} {φ : G.left ⟶ G₀.left} {φB : G₀.left ⟶ A.left}
    (h₁ : IsPullback φ G.hom G₀.hom g) (h₂ : IsPullback φB G₀.hom A.hom (𝟙 S₀)) (a : S₀ ⟶ A.left)
    (ha : a ≫ A.hom = 𝟙 S₀) : ∃ x : S ⟶ G.left, x ≫ φ ≫ φB = g ≫ a ∧ x ≫ G.hom = 𝟙 S := by
  let P := h₂.lift (g ≫ a) g (by rw [Category.assoc, ha, Category.comp_id])
  refine ⟨h₁.lift P (𝟙 S) (by rw [h₂.lift_snd, Category.id_comp]), ?_, h₁.lift_snd _ _ _⟩
  rw [← Category.assoc, h₁.lift_fst, h₂.lift_fst]

/- English proof (translation)
Apply `h₁.hom_ext` to reduce the goal to its premises. Apply `h₂.hom_ext` to reduce the goal to its premises. Simplify `hφ` using `only [Category.assoc]`. Rewrite using `[Category.assoc, Category.assoc, h₁.w, ← Category.assoc, hx, ← Category.assoc, hx']`. Rewrite using `[hx, hx']`.
-/
theorem pt_unique {G : Over S} {G₀ A : Over S₀} {g : S ⟶ S₀} {φ : G.left ⟶ G₀.left} {φB : G₀.left ⟶ A.left}
    (h₁ : IsPullback φ G.hom G₀.hom g) (h₂ : IsPullback φB G₀.hom A.hom (𝟙 S₀)) {Z : Scheme.{0}} (r : Z ⟶ S)
    (x x' : Z ⟶ G.left) (hφ : x ≫ φ ≫ φB = x' ≫ φ ≫ φB) (hx : x ≫ G.hom = r) (hx' : x' ≫ G.hom = r) : x = x' := by
  apply h₁.hom_ext
  · apply h₂.hom_ext
    · simpa only [Category.assoc] using hφ
    · rw [Category.assoc, Category.assoc, h₁.w, ← Category.assoc, hx, ← Category.assoc, hx']
  · rw [hx, hx']

/- English proof (translation)
Set `p₁` to `pushHom h₁ (𝟙_ (Over S))`. Set `p₂` to `pushHom h₂ (Over.mk ((𝟙_ (Over S)).hom ≫ g))`. Set `U : Over.mk (((𝟙_ (Over S)).hom ≫ g) ≫ 𝟙 S₀) ⟶ 𝟙_ (Over S₀)` to `toUnit _`. Establish `hU : U.left = g`. Use `Over.w U` as an intermediate fact.

Simplify `this` using `[unit_hom]`. Establish `e : p₂ (p₁ X) = preHom U a`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show (X.left ≫ φ) ≫ φB = U.left ≫ a.left`. Rewrite using `[Category.assoc, hX, hU]`.

Establish `e' : p₂ (p₁ (X ^ n)) = preHom U (a ^ n)`. Rewrite using `[map_pow, map_pow, e, map_pow]`. Use `congrArg (fun z => z.left) e'` as an intermediate fact. Rewrite using `[← Category.assoc]`. Use `this.trans ?_` and prove the remaining obligations.

Use `show U.left ≫ (a ^ n).left = _`. Rewrite using `[hU]`.
-/
theorem pow_left {G : Over S} {G₀ A : Over S₀} [GrpObj G] [GrpObj G₀] [GrpObj A] {g : S ⟶ S₀}
    {φ : G.left ⟶ G₀.left} {φB : G₀.left ⟶ A.left}
    (h₁ : IsGrpPullback G G₀ g φ) (h₂ : IsGrpPullback G₀ A (𝟙 S₀) φB) (X : 𝟙_ (Over S) ⟶ G)
    (a : 𝟙_ (Over S₀) ⟶ A) (hX : X.left ≫ φ ≫ φB = g ≫ a.left) (n : ℕ) :
    (X ^ n).left ≫ φ ≫ φB = g ≫ (a ^ n).left := by
  let p₁ := pushHom h₁ (𝟙_ (Over S))
  let p₂ := pushHom h₂ (Over.mk ((𝟙_ (Over S)).hom ≫ g))
  let U : Over.mk (((𝟙_ (Over S)).hom ≫ g) ≫ 𝟙 S₀) ⟶ 𝟙_ (Over S₀) := toUnit _
  have hU : U.left = g := by
    have := Over.w U
    simpa [unit_hom] using this
  have e : p₂ (p₁ X) = preHom U a := by
    apply Over.OverMorphism.ext
    show (X.left ≫ φ) ≫ φB = U.left ≫ a.left
    rw [Category.assoc, hX, hU]
  have e' : p₂ (p₁ (X ^ n)) = preHom U (a ^ n) := by
    rw [map_pow, map_pow, e, map_pow]
  have := congrArg (fun z => z.left) e'
  rw [← Category.assoc]
  refine this.trans ?_
  show U.left ≫ (a ^ n).left = _
  rw [hU]

/- English proof (translation)
Establish `hpadd : ∀ a b, D.c (a + b) = D.c a * D.c b` using `fun a b => by`. Rewrite using `[D.c_add, Hom.mul_def]`. Both sides reduce to the same expression. Proceed by induction on `n with`. Consider the case `zero`.

Establish `h` using `hpadd 0 0`. Rewrite `h` using `[add_zero]`. Rewrite using `[zero_smul, pow_zero]`. Conclude with `(mul_eq_left.1 h.symm)`. Consider the case `succ n ih => rw [succ_nsmul, hpadd, ih, pow_succ]`.
-/
theorem c_nsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (y : D.X) (n : ℕ) :
    D.c (n • y) = D.c y ^ n := by
  have hpadd : ∀ a b, D.c (a + b) = D.c a * D.c b := fun a b => by
    rw [D.c_add, Hom.mul_def]; rfl
  induction n with
  | zero =>
    have h := hpadd 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact (mul_eq_left.1 h.symm)
  | succ n ih => rw [succ_nsmul, hpadd, ih, pow_succ]

end GlobalTheory.UCanon.EpsPts

namespace GlobalTheory.UCanon

open GlobalTheory.UCanon.EpsPts in

/- English proof (translation)
Introduce `E _ _ _ H D' l c L k _ f o' m₁ m₂ n hn h0 u hu hu₁ hu₂`. Establish `hc : ∀ y, (L.D.c y).left ≫ L.D.P.A.hom = 𝟙 _` using `fun y => Over.w (L.D.c y)`. Establish `ex₁` using `fun y => exists_pt m₁.cart.1 L.ab.1.1 (L.D.c y).left (hc y)`. Establish `ex₂` using `fun y => exists_pt m₂.cart.1 L.ab.1.1 (L.D.c y).left (hc y)`. Use `choose x hx₁ hxG using ex₁`.

Use `choose x₂ hx₂ hx₂G using ex₂`. Use `haveI : IsCommMonObj o'.t.G := o'.t.comm`. Establish `hAb : IsAbelianScheme o'.t.G` using `⟨o'.t.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩`. Set `r : Sp k ⟶ Sp (DualNumber k)` to `spMap (TrivSqZeroExt.fstHom k k k).toRingHom`. Establish `hr : r ≫ spMap f = r ≫ spMap (GlobalTheory.RigChart.constHom f)`.

Simplify using `only [r, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Apply the tactic sequence `all_goals (ext z; simp [GlobalTheory.RigChart.constHom])`. Establish `heq : ∀ y, x y = x₂ y`. Introduce `y`.

Set `X : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G` to `Over.homMk (x y) (hxG y)`. Set `X₂ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G` to `Over.homMk (x₂ y) (hx₂G y)`. Establish `hpow : X ^ n = X₂ ^ n`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `e₁ : (X ^ n).left = u y`.

Apply `pt_unique m₁.cart.1 L.ab.1.1 (𝟙 _) _ _ _ (Over.w (X ^ n)) (hu y)` to reduce the goal to its premises. Rewrite using `[pow_left m₁.cart L.ab.1 X (L.D.c y) (hx₁ y) n, hu₁ y, c_nsmul]`. Establish `e₂ : (X₂ ^ n).left = u y`. Apply `pt_unique m₂.cart.1 L.ab.1.1 (𝟙 _) _ _ _ (Over.w (X₂ ^ n)) (hu y)` to reduce the goal to its premises. Rewrite using `[pow_left m₂.cart L.ab.1 X₂ (L.D.c y) (hx₂ y) n, hu₂ y, c_nsmul]`.

Rewrite using `[e₁, e₂]`. Establish `h0' : r ≫ X.left = r ≫ X₂.left` using `by show r ≫ x y = r ≫ x₂ y`. Establish `hh` using `h0 (Sp k) (r ≫ x₂ y) (𝟙 _) (by rw [Category.assoc, hx₂G, Category.comp_id, Category.id_comp])`. Establish `hh' : r ≫ x₂ y ≫ m₁.cm.F = r ≫ x₂ y ≫ m₂.cm.F` using `by simpa only [Category.assoc] using hh`. Establish `w₁ : x y ≫ m₁.cm.F ≫ L.o.t.G.hom = spMap f`.

Rewrite using `[m₁.cart.1.w, ← Category.assoc, hxG y, Category.id_comp]`. Establish `w₂ : x₂ y ≫ m₂.cm.F ≫ L.o.t.G.hom = spMap (GlobalTheory.RigChart.constHom f)`. Rewrite using `[m₂.cart.1.w, ← Category.assoc, hx₂G y, Category.id_comp]`. Apply `m₁.cart.1.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc]`.

Rewrite using `[hh']`. Apply `L.ab.1.1.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc]`. Rewrite using `[hx₁ y, hx₂ y, ← Category.assoc, hr, Category.assoc]`. Simplify using `only [Category.assoc]`.

Rewrite using `[w₁, w₂, hr]`. Simplify using `only [Category.assoc]`. Rewrite using `[hxG y, hx₂G y]`. Conclude with `congrArg (fun z => z.left) (eq_of_pow_eq_of_eq_at_closed k o'.t.G hAb n hn X X₂ hpow h0')`. Conclude with `⟨x, hx₁, fun y => heq y ▸ hx₂ y, hxG⟩`.
-/
theorem pts_eps_of_mul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (k : Type) [Field k] (f : L.W →+* DualNumber k) (o' : LowObj D' c (f.comp L.b)) (m₁ : ObjMap o' L.o (spMap f)) (m₂ : ObjMap o' L.o (spMap (GlobalTheory.RigChart.constHom f))) (n : ℕ), (n : k) ≠ 0 → (∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k), x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ m₁.toSABMap.φ = x ≫ m₂.toSABMap.φ) → ∀ u : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, u y ≫ o'.t.G.hom = 𝟙 _) → (∀ y, u y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c (n • y)).left) → (∀ y, u y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c (n • y)).left) → ∃ x : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, x y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ o'.t.G.hom = 𝟙 _) := by
  intro E _ _ _ H D' l c L k _ f o' m₁ m₂ n hn h0 u hu hu₁ hu₂
  have hc : ∀ y, (L.D.c y).left ≫ L.D.P.A.hom = 𝟙 _ := fun y => Over.w (L.D.c y)
  have ex₁ := fun y => exists_pt m₁.cart.1 L.ab.1.1 (L.D.c y).left (hc y)
  have ex₂ := fun y => exists_pt m₂.cart.1 L.ab.1.1 (L.D.c y).left (hc y)
  choose x hx₁ hxG using ex₁
  choose x₂ hx₂ hx₂G using ex₂
  haveI : IsCommMonObj o'.t.G := o'.t.comm
  have hAb : IsAbelianScheme o'.t.G := ⟨o'.t.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩
  let r : Sp k ⟶ Sp (DualNumber k) := spMap (TrivSqZeroExt.fstHom k k k).toRingHom
  have hr : r ≫ spMap f = r ≫ spMap (GlobalTheory.RigChart.constHom f) := by
    simp only [r, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    all_goals (ext z; simp [GlobalTheory.RigChart.constHom])
  have heq : ∀ y, x y = x₂ y := by
    intro y
    let X : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G := Over.homMk (x y) (hxG y)
    let X₂ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G := Over.homMk (x₂ y) (hx₂G y)
    have hpow : X ^ n = X₂ ^ n := by
      apply Over.OverMorphism.ext
      have e₁ : (X ^ n).left = u y := by
        apply pt_unique m₁.cart.1 L.ab.1.1 (𝟙 _) _ _ _ (Over.w (X ^ n)) (hu y)
        rw [pow_left m₁.cart L.ab.1 X (L.D.c y) (hx₁ y) n, hu₁ y, c_nsmul]
      have e₂ : (X₂ ^ n).left = u y := by
        apply pt_unique m₂.cart.1 L.ab.1.1 (𝟙 _) _ _ _ (Over.w (X₂ ^ n)) (hu y)
        rw [pow_left m₂.cart L.ab.1 X₂ (L.D.c y) (hx₂ y) n, hu₂ y, c_nsmul]
      rw [e₁, e₂]
    have h0' : r ≫ X.left = r ≫ X₂.left := by
      show r ≫ x y = r ≫ x₂ y
      have hh := h0 (Sp k) (r ≫ x₂ y) (𝟙 _) (by rw [Category.assoc, hx₂G, Category.comp_id, Category.id_comp])
      have hh' : r ≫ x₂ y ≫ m₁.cm.F = r ≫ x₂ y ≫ m₂.cm.F := by simpa only [Category.assoc] using hh
      have w₁ : x y ≫ m₁.cm.F ≫ L.o.t.G.hom = spMap f := by
        rw [m₁.cart.1.w, ← Category.assoc, hxG y, Category.id_comp]
      have w₂ : x₂ y ≫ m₂.cm.F ≫ L.o.t.G.hom = spMap (GlobalTheory.RigChart.constHom f) := by
        rw [m₂.cart.1.w, ← Category.assoc, hx₂G y, Category.id_comp]
      apply m₁.cart.1.hom_ext
      · simp only [Category.assoc]
        rw [hh']
        apply L.ab.1.1.hom_ext
        · simp only [Category.assoc]
          rw [hx₁ y, hx₂ y, ← Category.assoc, hr, Category.assoc]
        · simp only [Category.assoc]
          rw [w₁, w₂, hr]
      · simp only [Category.assoc]
        rw [hxG y, hx₂G y]
    exact congrArg (fun z => z.left) (eq_of_pow_eq_of_eq_at_closed k o'.t.G hAb n hn X X₂ hpow h0')
  exact ⟨x, hx₁, fun y => heq y ▸ hx₂ y, hxG⟩

end GlobalTheory.UCanon
