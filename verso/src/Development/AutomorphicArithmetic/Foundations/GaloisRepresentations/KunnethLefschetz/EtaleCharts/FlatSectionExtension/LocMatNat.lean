import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ = f.app ⊤`. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression.
-/
private theorem appLE_top_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  change _ = f.app ⊤
  rw [Scheme.Hom.app_eq_appLE]
  rfl

/- English proof (translation)
Establish `e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)` using `fun _ _ => trivial`. Rewrite using `[← appLE_top_eq f e]`. Conclude with `(Scheme.Hom.appLE_comp_appLE f g N ⊤ ⊤ h e).symm`.
-/
private theorem appLE_comp_appTop' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Opens)
    (h : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ N) (h' : (⊤ : X.Opens) ≤ (f ≫ g) ⁻¹ᵁ N) :
    (f ≫ g).appLE N ⊤ h' = g.appLE N ⊤ h ≫ f.appTop := by
  have e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := fun _ _ => trivial
  rw [← appLE_top_eq f e]
  exact (Scheme.Hom.appLE_comp_appLE f g N ⊤ ⊤ h e).symm

/- English proof (translation)
Introduce `K _ W Z Y q i π D d B α β V' V s p M h x'`. Take `⟨U, N, hx, hN, h₁, h₂, hU, G, hG, hM⟩` from `h (s x')`. Establish `e : (s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i = (s ∣_ U) ≫ U.ι ≫ p ≫ i`. Rewrite using `[← Category.assoc (s ∣_ U), morphismRestrict_ι]`. Simplify using `only [Category.assoc]`.

Establish `hU' : ⊤ ≤ ((s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i) ⁻¹ᵁ N`. Rewrite using `[e]`. Introduce `y _`. Conclude with `hU (Set.mem_univ ((s ∣_ U) y))`. Use `⟨s ⁻¹ᵁ U, N, hx, hN, h₁, h₂, hU', G, hG, ?_⟩` and prove the remaining obligations.

Establish `gen : ∀ (f g : ((s ⁻¹ᵁ U : V'.Opens) : Scheme.{0}) ⟶ Z) (_ : f = g) (hf : ⊤ ≤ f ⁻¹ᵁ N) (hg : ⊤ ≤ g ⁻¹ᵁ N), f.appLE N ⊤ hf = g.appLE N ⊤ hg`. Introduce and unpack `f g rfl _ _`. Both sides reduce to the same expression. Establish `h3 : ((s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i).appLE N ⊤ hU' = (U.ι ≫ p ≫ i).appLE N ⊤ hU ≫ (s ∣_ U).appTop` using `(gen _ _ e hU' (e ▸ hU')).trans (appLE_comp_appTop' _ _ N hU _)`. Establish `h4 : ∀ a : Γ(V, ⊤), (s ∣_ U).appTop.hom (U.ι.appTop.hom a) = (s ⁻¹ᵁ U).ι.appTop.hom (s.appTop.hom a)`.

Introduce `a`. Establish `e2 : ((s ∣_ U) ≫ U.ι).appTop = ((s ⁻¹ᵁ U).ι ≫ s).appTop` using `by rw [morphismRestrict_ι]`. Rewrite `e2` using `[Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]`. Conclude with `congrArg (fun φ => φ.hom a) e2`. Use extensionality with `m l`.

Establish `h1` using `congrFun (congrFun hM m) l`. Simplify using `only [Matrix.map_apply] at h1 ⊢`. Rewrite using `[h3, ← h4, h1]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatNat :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {V' V : Scheme.{0}} (s : V' ⟶ V) (p : V ⟶ W) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), LocMat B α β p M → LocMat B α β (s ≫ p) (M.map s.appTop.hom) := by
  intro K _ W Z Y q i π D d B α β V' V s p M h x'
  obtain ⟨U, N, hx, hN, h₁, h₂, hU, G, hG, hM⟩ := h (s x')
  have e : (s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i = (s ∣_ U) ≫ U.ι ≫ p ≫ i := by
    rw [← Category.assoc (s ∣_ U), morphismRestrict_ι]
    simp only [Category.assoc]
  have hU' : ⊤ ≤ ((s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i) ⁻¹ᵁ N := by
    rw [e]
    intro y _
    exact hU (Set.mem_univ ((s ∣_ U) y))
  refine ⟨s ⁻¹ᵁ U, N, hx, hN, h₁, h₂, hU', G, hG, ?_⟩
  have gen : ∀ (f g : ((s ⁻¹ᵁ U : V'.Opens) : Scheme.{0}) ⟶ Z) (_ : f = g) (hf : ⊤ ≤ f ⁻¹ᵁ N) (hg : ⊤ ≤ g ⁻¹ᵁ N),
      f.appLE N ⊤ hf = g.appLE N ⊤ hg := by
    rintro f g rfl _ _
    rfl
  have h3 : ((s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i).appLE N ⊤ hU' = (U.ι ≫ p ≫ i).appLE N ⊤ hU ≫ (s ∣_ U).appTop :=
    (gen _ _ e hU' (e ▸ hU')).trans (appLE_comp_appTop' _ _ N hU _)
  have h4 : ∀ a : Γ(V, ⊤), (s ∣_ U).appTop.hom (U.ι.appTop.hom a) = (s ⁻¹ᵁ U).ι.appTop.hom (s.appTop.hom a) := by
    intro a
    have e2 : ((s ∣_ U) ≫ U.ι).appTop = ((s ⁻¹ᵁ U).ι ≫ s).appTop := by rw [morphismRestrict_ι]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at e2
    exact congrArg (fun φ => φ.hom a) e2
  ext m l
  have h1 := congrFun (congrFun hM m) l
  simp only [Matrix.map_apply] at h1 ⊢
  rw [h3, ← h4, h1]
  rfl
