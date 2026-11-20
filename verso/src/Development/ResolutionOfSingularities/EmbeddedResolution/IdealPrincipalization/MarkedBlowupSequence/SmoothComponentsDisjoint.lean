import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.IrreducibleComponents
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

def IrreducibleComponentsDisjointOfSmooth : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)),
    AlgebraicGeometry.Smooth p →
    ∀ C₁ ∈ irreducibleComponents ↥X, ∀ C₂ ∈ irreducibleComponents ↥X,
      C₁ ≠ C₂ → Disjoint C₁ C₂

/- English proof (translation)
Introduce `k _ X p hp C₁ h₁ C₂ h₂ hne`. Establish `: AlgebraicGeometry.Smooth p` using `hp`. Rewrite using `[Set.disjoint_left]`. Introduce `x hx₁ hx₂`. Conclude with `hne (irreducibleComponents_eq_of_stalk_isDomain X (fun y => isDomain_stalk_of_smooth p y) h₁ h₂ hx₁ hx₂)`.
-/
theorem irreducibleComponentsDisjointOfSmooth : IrreducibleComponentsDisjointOfSmooth.{u} := by
  intro k _ X p hp C₁ h₁ C₂ h₂ hne
  have : AlgebraicGeometry.Smooth p := hp
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  exact hne
    (irreducibleComponents_eq_of_stalk_isDomain X
      (fun y => isDomain_stalk_of_smooth p y) h₁ h₂ hx₁ hx₂)

end FunctorialResolution.EmbeddedResolution
