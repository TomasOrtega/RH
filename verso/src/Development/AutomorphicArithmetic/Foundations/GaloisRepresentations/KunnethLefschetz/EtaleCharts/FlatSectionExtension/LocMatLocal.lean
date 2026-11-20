import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Introduce `K _ W Z Y q i π D d B α β V p M h x`. Take `⟨U, hxU, hL⟩` from `h x`. Take `⟨U', N, hx', hN, h₁, h₂, hU', G, hT, hM⟩` from `hL ⟨x, hxU⟩`. Establish `he : (U.ι.isoImage U').hom ≫ (U.ι ''ᵁ U').ι = U'.ι ≫ U.ι` using `U.ι.isoImage_hom_ι U'`. Establish `hU'' : ⊤ ≤ ((U.ι ''ᵁ U').ι ≫ p ≫ i) ⁻¹ᵁ N`.

Introduce and unpack `⟨y, z, hz, rfl⟩ _`. Use `@hU' (⟨z, hz⟩ : U'.toScheme) trivial` as an intermediate fact. Conclude with `this`. Use `⟨U.ι ''ᵁ U', N, ⟨⟨x, hxU⟩, hx', rfl⟩, hN, h₁, h₂, hU'', G, hT, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`.

Establish `hinj : ∀ {A C : Scheme.{0}} (e : A ≅ C), Function.Injective e.hom.appTop.hom`. Introduce `A C e`. Establish `: IsIso e.hom.appTop` using `inferInstanceAs (IsIso (e.hom.app ⊤))`. Conclude with `(ConcreteCategory.bijective_of_isIso e.hom.appTop).1`. Apply `hinj (U.ι.isoImage U')` to reduce the goal to its premises.

Establish `hab` using `congrFun (congrFun hM a) b`. Simplify using `only [Matrix.map_apply] at hab ⊢`. Establish `e₁ : (U.ι.isoImage U').hom.appTop.hom (((U.ι ''ᵁ U').ι).appTop.hom (M a b)) = U'.ι.appTop.hom (U.ι.appTop.hom (M a b))`. Rewrite using `[← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, he]`. Establish `e₂ : (U.ι.isoImage U').hom.appTop.hom ((((U.ι ''ᵁ U').ι ≫ p ≫ i).appLE N ⊤ hU'').hom (G a b)) = ((U'.ι ≫ (U.ι ≫ p) ≫ i).appLE N ⊤ hU').hom (G a b)`.

Establish `: ((U.ι ''ᵁ U').ι ≫ p ≫ i).appLE N ⊤ hU'' ≫ (U.ι.isoImage U').hom.appTop = (U'.ι ≫ (U.ι ≫ p) ≫ i).appLE N ⊤ hU'`. Establish `hc : U'.ι ≫ (U.ι ≫ p) ≫ i = (U.ι.isoImage U').hom ≫ (U.ι ''ᵁ U').ι ≫ p ≫ i`. Rewrite using `[reassoc_of% he]`. Simplify using the standard rewrite rules. Simplify using `only [hc]`.

Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Conclude with `Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _`. Conclude with `congrArg (fun f => f.hom (G a b)) this`. Rewrite using `[e₁, e₂, hab]`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatLocal :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {V : Scheme.{0}} (p : V ⟶ W) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), (∀ x : V, ∃ U : V.Opens, x ∈ U ∧ LocMat B α β (U.ι ≫ p) (M.map U.ι.appTop.hom)) → LocMat B α β p M := by
  intro K _ W Z Y q i π D d B α β V p M h x
  obtain ⟨U, hxU, hL⟩ := h x
  obtain ⟨U', N, hx', hN, h₁, h₂, hU', G, hT, hM⟩ := hL ⟨x, hxU⟩
  have he : (U.ι.isoImage U').hom ≫ (U.ι ''ᵁ U').ι = U'.ι ≫ U.ι := U.ι.isoImage_hom_ι U'
  have hU'' : ⊤ ≤ ((U.ι ''ᵁ U').ι ≫ p ≫ i) ⁻¹ᵁ N := by
    rintro ⟨y, z, hz, rfl⟩ _
    have := @hU' (⟨z, hz⟩ : U'.toScheme) trivial
    exact this
  refine ⟨U.ι ''ᵁ U', N, ⟨⟨x, hxU⟩, hx', rfl⟩, hN, h₁, h₂, hU'', G, hT, ?_⟩
  ext a b
  have hinj : ∀ {A C : Scheme.{0}} (e : A ≅ C), Function.Injective e.hom.appTop.hom := by
    intro A C e
    have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso e.hom.appTop).1
  apply hinj (U.ι.isoImage U')
  have hab := congrFun (congrFun hM a) b
  simp only [Matrix.map_apply] at hab ⊢
  have e₁ : (U.ι.isoImage U').hom.appTop.hom (((U.ι ''ᵁ U').ι).appTop.hom (M a b)) = U'.ι.appTop.hom (U.ι.appTop.hom (M a b)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, he]
  have e₂ : (U.ι.isoImage U').hom.appTop.hom ((((U.ι ''ᵁ U').ι ≫ p ≫ i).appLE N ⊤ hU'').hom (G a b)) = ((U'.ι ≫ (U.ι ≫ p) ≫ i).appLE N ⊤ hU').hom (G a b) := by
    have : ((U.ι ''ᵁ U').ι ≫ p ≫ i).appLE N ⊤ hU'' ≫ (U.ι.isoImage U').hom.appTop = (U'.ι ≫ (U.ι ≫ p) ≫ i).appLE N ⊤ hU' := by
      have hc : U'.ι ≫ (U.ι ≫ p) ≫ i = (U.ι.isoImage U').hom ≫ (U.ι ''ᵁ U').ι ≫ p ≫ i := by
        rw [reassoc_of% he]; simp
      simp only [hc]
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    exact congrArg (fun f => f.hom (G a b)) this
  rw [e₁, e₂, hab]
