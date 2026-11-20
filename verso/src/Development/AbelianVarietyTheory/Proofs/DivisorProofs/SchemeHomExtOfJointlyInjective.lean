import Mathlib
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

/- English proof (translation)
Introduce `Z Z₁ Z₂ X e₁ e₂ hcov hinj f g h₁ h₂`. Establish `hbase : f.base = g.base`. Use extensionality with `z`. Break down `hcov z with ⟨z₁, rfl⟩ | ⟨z₂, rfl⟩` into its components or cases. Use `congrArg (fun k : Z₁ ⟶ X => k z₁) h₁` as an intermediate fact.

Simplify `this` using `[Scheme.Hom.comp_apply]`. Use `congrArg (fun k : Z₂ ⟶ X => k z₂) h₂` as an intermediate fact. Simplify `this` using `[Scheme.Hom.comp_apply]`. Establish `key : ∀ {Y : Scheme.{0}} (e : Y ⟶ Z), e ≫ f = e ≫ g → ∀ U : X.Opens, (f.app U ≫ Z.presheaf.map (eqToHom congr((TopologicalSpace.Opens.map $hbase.symm).obj U)).op) ≫ e.app (g ⁻¹ᵁ U) = g.app U ≫ e.app (g ⁻¹ᵁ U)`. Introduce `Y e he U`.

Rewrite using `[Category.assoc, Scheme.Hom.naturality, ← Category.assoc, ← Scheme.Hom.comp_app, Scheme.Hom.congr_app he]`. Simplify using `[Scheme.Hom.comp_app]`. Use `conv_rhs => rw [← Category.comp_id (Scheme.Hom.app e (g ⁻¹ᵁ U))]`. Use `congr 2`. Conclude with `(Y.presheaf.map_comp _ _).symm.trans ((congrArg Y.presheaf.map (Subsingleton.elim _ _)).trans (Y.presheaf.map_id _))`.

Use `Scheme.Hom.ext hbase fun U => ?_` and prove the remaining obligations. Use extensionality with `s`. Apply `hinj (g ⁻¹ᵁ U)` to reduce the goal to its premises. Conclude with `congr(($(key e₁ h₁ U)).hom s)`. Conclude with `congr(($(key e₂ h₂ U)).hom s)`.
-/
theorem scheme_hom_ext_of_jointly_injective : ∀ (Z Z₁ Z₂ X : Scheme.{0}) (e₁ : Z₁ ⟶ Z) (e₂ : Z₂ ⟶ Z), (∀ z : Z, (∃ z₁, e₁ z₁ = z) ∨ ∃ z₂, e₂ z₂ = z) → (∀ (W : Z.Opens) (a b : Γ(Z, W)), e₁.app W a = e₁.app W b → e₂.app W a = e₂.app W b → a = b) → ∀ f g : Z ⟶ X, e₁ ≫ f = e₁ ≫ g → e₂ ≫ f = e₂ ≫ g → f = g := by
  intro Z Z₁ Z₂ X e₁ e₂ hcov hinj f g h₁ h₂
  have hbase : f.base = g.base := by
    ext z
    rcases hcov z with ⟨z₁, rfl⟩ | ⟨z₂, rfl⟩
    · have := congrArg (fun k : Z₁ ⟶ X => k z₁) h₁
      simpa [Scheme.Hom.comp_apply] using this
    · have := congrArg (fun k : Z₂ ⟶ X => k z₂) h₂
      simpa [Scheme.Hom.comp_apply] using this
  have key : ∀ {Y : Scheme.{0}} (e : Y ⟶ Z), e ≫ f = e ≫ g → ∀ U : X.Opens,
      (f.app U ≫ Z.presheaf.map (eqToHom congr((TopologicalSpace.Opens.map $hbase.symm).obj U)).op) ≫
        e.app (g ⁻¹ᵁ U) = g.app U ≫ e.app (g ⁻¹ᵁ U) := by
    intro Y e he U
    rw [Category.assoc, Scheme.Hom.naturality, ← Category.assoc, ← Scheme.Hom.comp_app,
      Scheme.Hom.congr_app he]
    simp [Scheme.Hom.comp_app]
    conv_rhs => rw [← Category.comp_id (Scheme.Hom.app e (g ⁻¹ᵁ U))]
    congr 2
    exact (Y.presheaf.map_comp _ _).symm.trans
      ((congrArg Y.presheaf.map (Subsingleton.elim _ _)).trans (Y.presheaf.map_id _))
  refine Scheme.Hom.ext hbase fun U => ?_
  ext s
  apply hinj (g ⁻¹ᵁ U)
  · exact congr(($(key e₁ h₁ U)).hom s)
  · exact congr(($(key e₂ h₂ U)).hom s)

end GlobalTheory
