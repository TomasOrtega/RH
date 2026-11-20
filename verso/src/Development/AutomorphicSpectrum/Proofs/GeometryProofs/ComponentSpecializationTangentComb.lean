import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValFam
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.Rep

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
  {φ : G'.left ⟶ G.left}

/- English proof (translation)
Substitute `hg` using the available equality. Conclude with `hφ.2 T x y x₀ y₀ hx hy`.
-/
theorem grpPull_mul (hφ : IsGrpPullback G' G f φ) (T : Over S') {g : T.left ⟶ S} (hg : g = T.hom ≫ f)
    (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hg
  exact hφ.2 T x y x₀ y₀ hx hy

/- English proof (translation)
Substitute `hg` using the available equality. Establish `hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f`. Rewrite using `[Category.assoc, hφ.1.w, ← Category.assoc]`. Conclude with `congrArg (· ≫ f) (Over.w (1 : T ⟶ G'))`. Set `e : Over.mk (T.hom ≫ f) ⟶ G` to `Over.homMk ((1 : T ⟶ G').left ≫ φ) hw`.

Establish `h` using `hφ.2 T 1 1 e e rfl rfl`. Rewrite `h` using `[_root_.mul_one]`. Establish `h2 : e * e = e` using `Over.OverMorphism.ext h`. Establish `h3 : e = 1` using `mul_eq_left.1 h2`. Conclude with `(congrArg (fun q : Over.mk (T.hom ≫ f) ⟶ G => q.left) h3).symm`.
-/
theorem grpPull_one (hφ : IsGrpPullback G' G f φ) (T : Over S') {g : T.left ⟶ S} (hg : g = T.hom ≫ f) :
    (1 : Over.mk g ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  subst hg
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc]
    exact congrArg (· ≫ f) (Over.w (1 : T ⟶ G'))
  let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have h := hφ.2 T 1 1 e e rfl rfl
  rw [_root_.mul_one] at h
  have h2 : e * e = e := Over.OverMorphism.ext h
  have h3 : e = 1 := mul_eq_left.1 h2
  exact (congrArg (fun q : Over.mk (T.hom ≫ f) ⟶ G => q.left) h3).symm

end Grp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Same

variable {Y : Model Xo c β} {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}

/- English proof (translation)
Set `T : Over (Xo.XF c)` to `epsAt y`. Use `⟨(1 : T ⟶ Y.oF.t.G).left, Over.w _, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(grpPull_one Y.m0.cart T (Category.assoc _ _ _).symm).symm`. Conclude with `(grpPull_one Y.m.cart T (Category.assoc _ _ _).symm).symm`.
-/
theorem sameVec_one (Y : Model Xo c β) (y : Sp F ⟶ Xo.XF c) : SameVec Y y 1 1 := by
  let T : Over (Xo.XF c) := epsAt y
  refine ⟨(1 : T ⟶ Y.oF.t.G).left, Over.w _, ?_, ?_⟩
  · exact (grpPull_one Y.m0.cart T (Category.assoc _ _ _).symm).symm
  · exact (grpPull_one Y.m.cart T (Category.assoc _ _ _).symm).symm

/- English proof (translation)
Take `⟨u₁, p₁, q₁, r₁⟩` from `h₁`. Take `⟨u₂, p₂, q₂, r₂⟩` from `h₂`. Set `T : Over (Xo.XF c)` to `epsAt y`. Set `x₁ : T ⟶ Y.oF.t.G` to `Over.homMk u₁ p₁`. Set `x₂ : T ⟶ Y.oF.t.G` to `Over.homMk u₂ p₂`.

Use `⟨(x₁ * x₂).left, Over.w (x₁ * x₂), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(grpPull_mul Y.m0.cart T (Category.assoc _ _ _).symm x₁ x₂ a b q₁.symm q₂.symm).symm`. Conclude with `(grpPull_mul Y.m.cart T (Category.assoc _ _ _).symm x₁ x₂ a' b' r₁.symm r₂.symm).symm`.
-/
theorem sameVec_mul {a b : epsAt (under y) ⟶ Xo.univ.t.G} {a' b' : epsAt (y ≫ Y.j) ⟶ Y.t.G}
    (h₁ : SameVec Y y a a') (h₂ : SameVec Y y b b') : SameVec Y y (a * b) (a' * b') := by
  obtain ⟨u₁, p₁, q₁, r₁⟩ := h₁
  obtain ⟨u₂, p₂, q₂, r₂⟩ := h₂
  let T : Over (Xo.XF c) := epsAt y
  let x₁ : T ⟶ Y.oF.t.G := Over.homMk u₁ p₁
  let x₂ : T ⟶ Y.oF.t.G := Over.homMk u₂ p₂
  refine ⟨(x₁ * x₂).left, Over.w (x₁ * x₂), ?_, ?_⟩
  · exact (grpPull_mul Y.m0.cart T (Category.assoc _ _ _).symm x₁ x₂ a b q₁.symm q₂.symm).symm
  · exact (grpPull_mul Y.m.cart T (Category.assoc _ _ _).symm x₁ x₂ a' b' r₁.symm r₂.symm).symm

/- English proof (translation)
Take `⟨u₀, p, q, t⟩` from `h`. Use `⟨spMap (GlobalTheory.CompanionTheory.Ar.epsMul r) ≫ u₀, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, p, ← Category.assoc, LieTangent.spec_eps_alg]`. Rewrite using `[Category.assoc, q, hu]`. Rewrite using `[Category.assoc, t]`.

Both sides reduce to the same expression.
-/
theorem sameVec_scale {a u : epsAt (under y) ⟶ Xo.univ.t.G} {a' : epsAt (y ≫ Y.j) ⟶ Y.t.G} (h : SameVec Y y a a')
    (r : F) (hu : u.left = spMap (GlobalTheory.CompanionTheory.Ar.epsMul r) ≫ a.left) :
    SameVec Y y u (LieTangent.epsScale (y ≫ Y.j) r ≫ a') := by
  obtain ⟨u₀, p, q, t⟩ := h
  refine ⟨spMap (GlobalTheory.CompanionTheory.Ar.epsMul r) ≫ u₀, ?_, ?_, ?_⟩
  · rw [Category.assoc, p, ← Category.assoc, LieTangent.spec_eps_alg]
  · rw [Category.assoc, q, hu]
  · rw [Category.assoc, t]
    rfl

end Same

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use `⟨1, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using Z.M.valAt_zero hg`. Simplify using `using sameVec_one Y y`.

Consider the case `succ n ih`. Take `⟨a, ha, hb⟩` from `h 0`. Take `⟨w', hw, hs⟩` from `ih (fun i => e i.succ) (fun i => u i.succ) fun i => h i.succ`. Use `⟨a * w', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_succ]`.

Conclude with `ha.add hw`. Rewrite using `[List.ofFn_succ, List.prod_cons]`. Conclude with `sameVec_mul hb hs`.
-/
theorem valFam_sum {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) {F : Type} [Field F]
    (y : Sp F ⟶ Xo.XF c) (hg : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) {n : ℕ} (e : Fin n → Z.V)
    (u : Fin n → (epsAt (under y) ⟶ Xo.univ.t.G))
    (h : ∀ j, ∃ a, Z.M.ValAt (y ≫ Y.j) (e j) a ∧ SameVec Y y (u j) a) :
    ∃ w', Z.M.ValAt (y ≫ Y.j) (∑ j, e j) w' ∧ SameVec Y y (List.ofFn u).prod w' := by
  induction n with
  | zero =>
    refine ⟨1, ?_, ?_⟩
    · simpa using Z.M.valAt_zero hg
    · simpa using sameVec_one Y y
  | succ n ih =>
    obtain ⟨a, ha, hb⟩ := h 0
    obtain ⟨w', hw, hs⟩ := ih (fun i => e i.succ) (fun i => u i.succ) fun i => h i.succ
    refine ⟨a * w', ?_, ?_⟩
    · rw [Fin.sum_univ_succ]
      exact ha.add hw
    · rw [List.ofFn_succ, List.prod_cons]
      exact sameVec_mul hb hs

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y U Z F _ y n b v s r w hg h hs hw`. Take `⟨u, hu, rfl⟩` from `hw`. Use `valFam_sum Z y hg _ u fun j => ?_` and prove the remaining obligations. Take `⟨h1, t, e1, e2⟩` from `hs j`. Take `⟨a, ha, hb⟩` from `h j`.

Establish `h2` using `ha.smul h1 t`. Rewrite `h2` using `[e1, e2]`. Conclude with `⟨_, h2, sameVec_scale hb (r j) (hu j)⟩`.
-/
theorem valFam_sum_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c) (n : ℕ) (b : Fin n → Z.V) (v : Vecs y n) (s : Fin n → Z.Ω) (r : Fin n → F) (w : epsAt (under y) ⟶ Xo.univ.t.G), genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) → IsValFam Z y b v → (∀ j, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (s j) (r j)) → IsComb r v w → ∃ w', Z.M.ValAt (y ≫ Y.j) (∑ j, s j • b j) w' ∧ SameVec Y y w w' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z F _ y n b v s r w hg h hs hw
  obtain ⟨u, hu, rfl⟩ := hw
  refine valFam_sum Z y hg _ u fun j => ?_
  obtain ⟨h1, t, e1, e2⟩ := hs j
  obtain ⟨a, ha, hb⟩ := h j
  have h2 := ha.smul h1 t
  rw [e1, e2] at h2
  exact ⟨_, h2, sameVec_scale hb (r j) (hu j)⟩

end GlobalTheory.CompanionTheory.Ar.Flat.Rep
