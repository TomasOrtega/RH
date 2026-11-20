import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfIsQProjOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

/- English proof (translation)
Establish `w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g` using `by rw [m.cart.1.w, Category.assoc]`. Use `set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w`. Establish `hφ : φ ≫ m₂.φ = m.φ` using `m₂.cart.1.lift_fst _ _ _`. Establish `hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f` using `m₂.cart.1.lift_snd _ _ _`. Establish `n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ)` using `by rw [hφ]; exact m.cart`.

Take `⟨φ₂, sq⟩` from `MapComp.exists_isSquare hφ'`. Establish `e : m.φ₂ = φ₂ ≫ m₂.φ₂` using `MapComp.isSquare_unique m.sq (hφ ▸ MapComp.isSquare_comp sq m₂.sq)`. Establish `hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left`. Introduce `c`. Apply `m₂.cart.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]`. Rewrite using `[Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']`. Establish `heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left`. Introduce `y`. Apply `m₂.cart.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]`. Rewrite using `[Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w] show 𝟙 _ ≫ f = f ≫ 𝟙 _`. Rewrite using `[Category.id_comp, Category.comp_id]`. Conclude with `⟨{ φ := φ φ₂ := φ₂ cart := m₂.cart.cancel n hφ' sq := sq act := hact pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol (LBIso.symm (MapComp.lbIso_pull_comp m₂.pol φ₂ e)) eta := heta }, hφ⟩`.
-/
theorem exists_objMap_cancel_φ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : ObjMap o₁ o₃ (f ≫ g)) (m₂ : ObjMap o₂ o₃ g) : ∃ m₁ : ObjMap o₁ o₂ f, m₁.φ ≫ m₂.φ = m.φ := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := MapComp.exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := MapComp.isSquare_unique m.sq (hφ ▸ MapComp.isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (MapComp.lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }, hφ⟩

/- English proof (translation)
Introduce `p _ D R _ b N h M X s s₁ u lev hU ρ hρ σ hσ S t o Y t₁ lu o' m lv' hlv' hlev y my hmy hys hys₁ r hrt hr a`. Establish `cast : ∀ {f f' : Y.left ⟶ S} (_ : f = f') (m₀ : ObjMap o' o f), ∃ m' : ObjMap o' o f', m'.φ = m₀.φ`. Introduce `f f' e m₀`. Substitute `e` using the available equality. Conclude with `⟨m₀, rfl⟩`.

Establish `hrY : (r a).left ≫ Y.hom = Y.hom` using `Over.w (r a)`. Take `⟨ma, hma⟩` from `(hρ a).2.2`. Establish `h₁ : (y ≫ ρ a) ≫ s = Y.hom ≫ t ∧ (y ≫ ρ a) ≫ s₁ = t₁ ≫ spMap (σ a) ∧ ∃ m' : ObjMap o' u (y ≫ ρ a), ∀ c, (sympTwist a lv' c).left ≫ m'.φ = (y ≫ ρ a) ≫ (lev c).left`. Use `⟨by rw [Category.assoc, (hρ a).1, hys], by rw [Category.assoc, hσ, ← Category.assoc, hys₁], my.comp ma, fun c => ?_⟩` and prove the remaining obligations. Establish `e₁` using `hmy (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M c)))`.

Establish `e₂` using `hma c`. Simplify using `only [sympTwist] at e₂ ⊢`. Express the relevant statement in the definitionally equal form `_ ≫ my.φ ≫ ma.φ = _`. Rewrite using `[← Category.assoc, e₁, Category.assoc, e₂, Category.assoc]`. Take `⟨mr, hmr⟩` from `cast hrY.symm m`.

Take `⟨m₂, hφ⟩` from `exists_objMap_cancel_φ mr m`. Rewrite `hφ` using `[hmr]`. Establish `hpull : ∀ c, (sympTwist a lv' c).left ≫ m₂.φ = (r a).left ≫ (lv' c).left`. Introduce `c`. Apply `m.cart.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, hφ, Category.assoc, hlv' c]`. Simplify using `only [sympTwist] at hlv' ⊢`. Rewrite using `[hlv', ← Over.comp_left, hr a c]`. Both sides reduce to the same expression. Rewrite using `[Category.assoc, m₂.cart.1.w, ← Category.assoc, Over.w (sympTwist a lv' c), Category.assoc, Over.w (lv' c)]`.

Simplify using the standard rewrite rules. Establish `h₂ : ((r a).left ≫ y) ≫ s = Y.hom ≫ t ∧ ((r a).left ≫ y) ≫ s₁ = t₁ ≫ spMap (σ a) ∧ ∃ m' : ObjMap o' u ((r a).left ≫ y), ∀ c, (sympTwist a lv' c).left ≫ m'.φ = ((r a).left ≫ y) ≫ (lev c).left`. Use `⟨by rw [Category.assoc, hys, ← Category.assoc, hrY], by rw [Category.assoc, hys₁, hrt], m₂.comp my, fun c => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ≫ m₂.φ ≫ my.φ = _`. Rewrite using `[← Category.assoc, hpull c, Category.assoc, hmy c, Category.assoc]`.

Conclude with `(hU Y.left (Y.hom ≫ t) (t₁ ≫ spMap (σ a)) o' (sympTwist a lv') (hlev a)).unique h₂ h₁`.
-/
theorem classify_equivariant : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
  (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)), HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
  ∀ (ρ : sympSimGrp h M → (X ⟶ X)), SympActs s s₁ u lev ρ →
  ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)), (∀ a, ρ a ≫ s₁ = s₁ ≫ spMap (σ a)) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Y : Over S) (t₁ : Y.left ⟶ Sp (cycAway M))
    (lu : (Fin h ⊕ Fin h → ℤ) → (Y ⟶ o.A)) (o' : Obj b N (Y.hom ≫ t)) (m : ObjMap o' o Y.hom)
    (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y.left) ⟶ o'.A)), (∀ a, (lv' a).left ≫ m.φ = (lu a).left) →
    (∀ a, IsSympLev o'.P h M (zetaAway M) (t₁ ≫ spMap (σ a)) (sympTwist a lv')) →
    ∀ (y : Y.left ⟶ X) (my : ObjMap o' u y), (∀ a, (lv' a).left ≫ my.φ = y ≫ (lev a).left) →
    y ≫ s = Y.hom ≫ t → y ≫ s₁ = t₁ →
    ∀ (r : sympSimGrp h M → (Y ⟶ Y)), (∀ a, (r a).left ≫ t₁ = t₁ ≫ spMap (σ a)) →
    (∀ a c, r a ≫ lu c = sympTwist a lu c) → ∀ a, (r a).left ≫ y = y ≫ ρ a := by
  intro p _ D R _ b N h M X s s₁ u lev hU ρ hρ σ hσ S t o Y t₁ lu o' m lv' hlv' hlev y my hmy hys hys₁ r hrt hr a
  have cast : ∀ {f f' : Y.left ⟶ S} (_ : f = f') (m₀ : ObjMap o' o f), ∃ m' : ObjMap o' o f', m'.φ = m₀.φ := by
    intro f f' e m₀; subst e; exact ⟨m₀, rfl⟩
  have hrY : (r a).left ≫ Y.hom = Y.hom := Over.w (r a)
  obtain ⟨ma, hma⟩ := (hρ a).2.2

  have h₁ : (y ≫ ρ a) ≫ s = Y.hom ≫ t ∧ (y ≫ ρ a) ≫ s₁ = t₁ ≫ spMap (σ a) ∧
      ∃ m' : ObjMap o' u (y ≫ ρ a), ∀ c, (sympTwist a lv' c).left ≫ m'.φ = (y ≫ ρ a) ≫ (lev c).left := by
    refine ⟨by rw [Category.assoc, (hρ a).1, hys], by rw [Category.assoc, hσ, ← Category.assoc, hys₁],
      my.comp ma, fun c => ?_⟩
    have e₁ := hmy (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M c)))
    have e₂ := hma c
    simp only [sympTwist] at e₂ ⊢
    change _ ≫ my.φ ≫ ma.φ = _
    rw [← Category.assoc, e₁, Category.assoc, e₂, Category.assoc]

  obtain ⟨mr, hmr⟩ := cast hrY.symm m
  obtain ⟨m₂, hφ⟩ := exists_objMap_cancel_φ mr m
  rw [hmr] at hφ
  have hpull : ∀ c, (sympTwist a lv' c).left ≫ m₂.φ = (r a).left ≫ (lv' c).left := by
    intro c
    apply m.cart.1.hom_ext
    · rw [Category.assoc, hφ, Category.assoc, hlv' c]
      simp only [sympTwist] at hlv' ⊢
      rw [hlv', ← Over.comp_left, hr a c]
      rfl
    · rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, Over.w (sympTwist a lv' c), Category.assoc,
        Over.w (lv' c)]
      simp
  have h₂ : ((r a).left ≫ y) ≫ s = Y.hom ≫ t ∧ ((r a).left ≫ y) ≫ s₁ = t₁ ≫ spMap (σ a) ∧
      ∃ m' : ObjMap o' u ((r a).left ≫ y), ∀ c, (sympTwist a lv' c).left ≫ m'.φ = ((r a).left ≫ y) ≫ (lev c).left := by
    refine ⟨by rw [Category.assoc, hys, ← Category.assoc, hrY], by rw [Category.assoc, hys₁, hrt],
      m₂.comp my, fun c => ?_⟩
    change _ ≫ m₂.φ ≫ my.φ = _
    rw [← Category.assoc, hpull c, Category.assoc, hmy c, Category.assoc]
  exact (hU Y.left (Y.hom ≫ t) (t₁ ≫ spMap (σ a)) o' (sympTwist a lv') (hlev a)).unique h₂ h₁

end GlobalTheory.HTSympCover
