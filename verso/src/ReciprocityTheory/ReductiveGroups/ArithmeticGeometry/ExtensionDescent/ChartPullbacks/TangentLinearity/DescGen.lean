import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.FnOfComp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

/- English proof (translation)
Establish `hE : EffectiveEpi Q`. Conclude with `inferInstance`. Take `⟨e, he⟩ : ∃ e, ∀ i : Fin 1, AffineSpace.toSpecMvPolyIntEquiv (Fin 1) e i = ρ` from `⟨(AffineSpace.toSpecMvPolyIntEquiv (Fin 1)).symm fun _ => ρ, fun i => by simp⟩`. Establish `hcomp : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (i : Fin 1), AffineSpace.toSpecMvPolyIntEquiv (Fin 1) (g ≫ e) i = g.appTop.hom ρ`. Introduce `Z g i`.

Rewrite using `[AffineSpace.toSpecMvPolyIntEquiv_comp, he]`. Establish `hdesc : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ X), g₁ ≫ Q = g₂ ≫ Q → g₁ ≫ e = g₂ ≫ e`. Introduce `Z g₁ g₂ h`. Apply `(AffineSpace.toSpecMvPolyIntEquiv (Fin 1)).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Rewrite using `[hcomp, hcomp]`. Conclude with `hρ g₁ g₂ h`. Use `⟨AffineSpace.toSpecMvPolyIntEquiv (Fin 1) (EffectiveEpi.desc Q e hdesc) 0, ?_⟩` and prove the remaining obligations. Establish `hf : AffineSpace.toSpecMvPolyIntEquiv (Fin 1) (Q ≫ EffectiveEpi.desc Q e hdesc) 0 = ρ`. Rewrite using `[EffectiveEpi.fac, he]`.

Rewrite `hf` using `[AffineSpace.toSpecMvPolyIntEquiv_comp]`. Conclude with `hf`.
-/
theorem descend_gen {X Y : Scheme.{0}} (Q : X ⟶ Y) [Flat Q] [Surjective Q] [IsAffineHom Q]
    (ρ : Γ(X, ⊤))
    (hρ : ∀ {Z : Scheme.{0}} (y1 y2 : Z ⟶ X), y1 ≫ Q = y2 ≫ Q → y1.appTop.hom ρ = y2.appTop.hom ρ) :
    ∃ v : Γ(Y, ⊤), Q.appTop.hom v = ρ := by

  have hE : EffectiveEpi Q := by
    exact inferInstance

  obtain ⟨e, he⟩ : ∃ e, ∀ i : Fin 1, AffineSpace.toSpecMvPolyIntEquiv (Fin 1) e i = ρ :=
    ⟨(AffineSpace.toSpecMvPolyIntEquiv (Fin 1)).symm fun _ => ρ, fun i => by simp⟩
  have hcomp : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (i : Fin 1),
      AffineSpace.toSpecMvPolyIntEquiv (Fin 1) (g ≫ e) i = g.appTop.hom ρ := by
    intro Z g i
    rw [AffineSpace.toSpecMvPolyIntEquiv_comp, he]
  have hdesc : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ X), g₁ ≫ Q = g₂ ≫ Q → g₁ ≫ e = g₂ ≫ e := by
    intro Z g₁ g₂ h
    apply (AffineSpace.toSpecMvPolyIntEquiv (Fin 1)).injective
    funext i
    rw [hcomp, hcomp]
    exact hρ g₁ g₂ h
  refine ⟨AffineSpace.toSpecMvPolyIntEquiv (Fin 1) (EffectiveEpi.desc Q e hdesc) 0, ?_⟩
  have hf : AffineSpace.toSpecMvPolyIntEquiv (Fin 1) (Q ≫ EffectiveEpi.desc Q e hdesc) 0 = ρ := by
    rw [EffectiveEpi.fac, he]
  rw [AffineSpace.toSpecMvPolyIntEquiv_comp] at hf
  exact hf

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
