import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProjectiveBundleFormulaTorsion

set_option backward.isDefEq.respectTransparency false

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.Di
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.Di.ChernBaseChange

private def sq {Y Y' X : Scheme.{0}} (f : Y ⟶ X) (f' : Y' ⟶ X) (τ : Y ⟶ Y') (hτ : τ ≫ f' = f) :
    Arrow.mk (yoneda.map f) ⟶ Arrow.mk (yoneda.map f') :=
  Arrow.homMk (yoneda.map τ) (𝟙 _) (by simp [← Functor.map_comp, hτ])

private def cm {Y Y' X : Scheme.{0}} (f : Y ⟶ X) (f' : Y' ⟶ X) (τ : Y ⟶ Y') (hτ : τ ≫ f' = f) : cech f ⟶ cech f' :=
  Arrow.mapCechNerve (sq f f' τ hτ)

/- English proof (translation)
Use `((Arrow.mapAugmentedCechNerve (sq f f' τ hτ)).w).trans ?_` and prove the remaining obligations. Conclude with `(congrArg (fun t => (Arrow.mk (yoneda.map f)).augmentedCechNerve.hom ≫ t) (CategoryTheory.Functor.map_id (SimplicialObject.const _) (yoneda.obj X))).trans (Category.comp_id _)`.
-/
private theorem cm_aug {Y Y' X : Scheme.{0}} (f : Y ⟶ X) (f' : Y' ⟶ X) (τ : Y ⟶ Y') (hτ : τ ≫ f' = f) :
    cm f f' τ hτ ≫ cechAug f' = cechAug f := by
  refine ((Arrow.mapAugmentedCechNerve (sq f f' τ hτ)).w).trans ?_
  exact (congrArg (fun t => (Arrow.mk (yoneda.map f)).augmentedCechNerve.hom ≫ t)
    (CategoryTheory.Functor.map_id (SimplicialObject.const _) (yoneda.obj X))).trans (Category.comp_id _)

/- English proof (translation)
Establish `e : WidePullback.lift (arrows` using `fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x) (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i]) ≫ (cm f f' τ hτ).app (op (SimplexCategory.mk k)) = WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f') (yoneda.map x) (fun i => yoneda.map (y i …`. Apply `WidePullback.hom_ext` to reduce the goal to its premises. Introduce `j`. Simplify using `[cm, sq, Arrow.mapCechNerve]`. Simplify using `[cm, sq, Arrow.mapCechNerve]`.

Conclude with `congrArg (fun t => t.app (op U) (𝟙 U)) e`.
-/
private theorem cm_pt {Y Y' X : Scheme.{0}} (f : Y ⟶ X) (f' : Y' ⟶ X) (τ : Y ⟶ Y') (hτ : τ ≫ f' = f) (k : ℕ)
    {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x) :
    ((cm f f' τ hτ).app (op (SimplexCategory.mk k))).app (op U) (cechPt f k x y h) =
      cechPt f' k x (fun i => y i ≫ τ) (fun i => by rw [Category.assoc, hτ, h]) := by
  have e : WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x) (fun i => yoneda.map (y i))
        (fun i => by rw [← yoneda.map_comp, h i]) ≫ (cm f f' τ hτ).app (op (SimplexCategory.mk k)) =
      WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f') (yoneda.map x) (fun i => yoneda.map (y i ≫ τ))
        (fun i => by rw [← yoneda.map_comp, Category.assoc, hτ, h i]) := by
    apply WidePullback.hom_ext
    · intro j
      simp [cm, sq, Arrow.mapCechNerve]
    · simp [cm, sq, Arrow.mapCechNerve]
  exact congrArg (fun t => t.app (op U) (𝟙 U)) e

/- English proof (translation)
Introduce `U ⟨x⟩`. Set `s : U ⟶ Y` to `(WidePullback.π (fun _ : Fin 1 => yoneda.map f) 0).app (op U) x`. Establish `h` using `hq.map ((s ≫ f).appTop).hom`. Simplify using `using h`.
-/
private theorem cech_inv (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) (hq : IsUnit (q : Γ(X, ⊤))) : Inv q (cech f) := by
  intro U ⟨x⟩
  let s : U ⟶ Y := (WidePullback.π (fun _ : Fin 1 => yoneda.map f) 0).app (op U) x
  have h := hq.map ((s ≫ f).appTop).hom
  simpa using h

/- English proof (translation)
Substitute `ha hb` using the available equality. Both sides reduce to the same expression.
-/
private theorem u_congr {X : Scheme.{0}} (D : CrystallineSemistableComparison.E.LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y}
    (ha : a = a') (hb : b = b') (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a' b' h' := by
  subst ha hb
  rfl

end UpperTheory.Gal.KunnethLefschetz.Di.ChernBaseChange

open UpperTheory.Gal.KunnethLefschetz.Di.ChernBaseChange in
/- English proof (translation)
Introduce `hI q _ Y Y₁ Y₂ D a c D' π hBC hq x ⟨L, hL, hx⟩`. Take `⟨h1, h2, h3⟩` from `hBC`. Set `π₂ : ((D.pb a).pb c).Y ⟶ D.Y` to `pullback.fst (D.pb a).f c ≫ pullback.fst D.f a`. Establish `hπ : π₂ ≫ D.f = ((D.pb a).pb c).f ≫ c ≫ a`. Establish `e₁ : pullback.fst (D.pb a).f c ≫ (D.pb a).f = ((D.pb a).pb c).f ≫ c` using `pullback.condition`.

Establish `e₂ : pullback.fst D.f a ≫ D.f = (D.pb a).f ≫ a` using `pullback.condition`. Express the relevant statement in the definitionally equal form `(pullback.fst (D.pb a).f c ≫ pullback.fst D.f a) ≫ D.f = _`. Rewrite using `[Category.assoc, e₂, ← Category.assoc, e₁, Category.assoc]`. Take `⟨τ, hτ, hτf⟩` from `h2 _ π₂ _ hπ`. Use `⟨cm _ _ τ hτf ≫ L, ?_, ?_⟩` and prove the remaining obligations.

Introduce `V z b hb`. Express the relevant statement in the definitionally equal form `lineUnit L (((cm _ _ τ hτf).app (op (SimplexCategory.mk 1))).app (op V) (cechPt _ 1 z b hb)) = _`. Establish `hh : ((b 0 ≫ τ) ≫ π) ≫ D.f = ((b 1 ≫ τ) ≫ π) ≫ D.f`. Simplify using `only [Category.assoc, h1]`. Rewrite using `[← Category.assoc τ, hτf, ← Category.assoc (b 0), ← Category.assoc (b 1), hb 0, hb 1]`.

Rewrite using `[cm_pt, hL, h3 V _ _ _ hh]`. Conclude with `u_congr D (by simp only [Category.assoc, hτ]; rfl) (by simp only [Category.assoc, hτ]; rfl) _ _`. Establish `hinv` using `cech_inv q D'.f hq`. Establish `e` using `(hI.a6nat q).2.2.1 (cm _ _ τ hτf) L hinv`. Rewrite using `[← e, ← hx, ← pull_comp, cm_aug]`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.Di.first_chern_class_isBaseChange :
    UpperTheory.Gal.KunnethLefschetz.Di.FirstChernClassBaseChange := by
  intro hI q _ Y Y₁ Y₂ D a c D' π hBC hq x ⟨L, hL, hx⟩
  obtain ⟨h1, h2, h3⟩ := hBC
  let π₂ : ((D.pb a).pb c).Y ⟶ D.Y := pullback.fst (D.pb a).f c ≫ pullback.fst D.f a
  have hπ : π₂ ≫ D.f = ((D.pb a).pb c).f ≫ c ≫ a := by
    have e₁ : pullback.fst (D.pb a).f c ≫ (D.pb a).f = ((D.pb a).pb c).f ≫ c := pullback.condition
    have e₂ : pullback.fst D.f a ≫ D.f = (D.pb a).f ≫ a := pullback.condition
    change (pullback.fst (D.pb a).f c ≫ pullback.fst D.f a) ≫ D.f = _
    rw [Category.assoc, e₂, ← Category.assoc, e₁, Category.assoc]
  obtain ⟨τ, hτ, hτf⟩ := h2 _ π₂ _ hπ
  refine ⟨cm _ _ τ hτf ≫ L, ?_, ?_⟩
  · intro V z b hb
    change lineUnit L (((cm _ _ τ hτf).app (op (SimplexCategory.mk 1))).app (op V) (cechPt _ 1 z b hb)) = _
    have hh : ((b 0 ≫ τ) ≫ π) ≫ D.f = ((b 1 ≫ τ) ≫ π) ≫ D.f := by
      simp only [Category.assoc, h1]
      rw [← Category.assoc τ, hτf, ← Category.assoc (b 0), ← Category.assoc (b 1), hb 0, hb 1]
    rw [cm_pt, hL, h3 V _ _ _ hh]
    exact u_congr D (by simp only [Category.assoc, hτ]; rfl) (by simp only [Category.assoc, hτ]; rfl) _ _
  · have hinv := cech_inv q D'.f hq
    have e := (hI.a6nat q).2.2.1 (cm _ _ τ hτf) L hinv
    rw [← e, ← hx, ← pull_comp, cm_aug]
