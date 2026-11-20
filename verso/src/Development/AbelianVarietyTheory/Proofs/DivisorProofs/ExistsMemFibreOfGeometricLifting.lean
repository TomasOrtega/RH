import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ S P' X π h a q hπ x hx H`. Take `⟨s₀, hs₀⟩` from `π.surjective (h x)`. Take `⟨w, hw, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := h) (g := π) x s₀ hs₀.symm`. Set `Ω : Type` to `AlgebraicClosure ((pullback h π).residueField w)`. Set `t : Sp Ω ⟶ pullback h π` to `Spec.map (CommRingCat.ofHom (algebraMap ((pullback h π).residueField w) Ω)) ≫ (pullback h π).fromSpecResidueField w`.

Establish `ht : ∀ y, t y = w`. Introduce `y`. Simplify using `only [t, Scheme.Hom.comp_apply]`. Conclude with `Scheme.fromSpecResidueField_apply _ _`. Establish `hξ : ∀ y, (t ≫ pullback.fst h π) y = x`.

Introduce `y`. Rewrite using `[Scheme.Hom.comp_apply, ht, hw]`. Take `⟨p, hp, -⟩` from `H Ω (t ≫ pullback.fst h π) (t ≫ pullback.snd h π) (by`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, rfl⟩`. Conclude with `hξ u`. Introduce and unpack `rfl`. Conclude with `⟨closedPoint Ω, hξ _⟩)`. Use the proof step `(by simp [pullback.condition])`.

Use `⟨p (closedPoint Ω), ?_⟩` and prove the remaining obligations. Establish `h₀` using `hξ (closedPoint Ω)`. Rewrite `h₀` using `[← hp]`. Conclude with `(Scheme.Hom.comp_apply p a _).symm.trans h₀`.
-/
theorem exists_mem_fibre_of_geometric_lifting :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (S P' X : Scheme.{0}) (π : S ⟶ Sp R) (h : P' ⟶ Sp R) (a : X ⟶ P') (q : X ⟶ S), Surjective π → ∀ x : P', h x = closedPoint R → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ h = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ q = s) → ∃ z : X, a z = x := by
  intro R _ _ S P' X π h a q hπ x hx H
  obtain ⟨s₀, hs₀⟩ := π.surjective (h x)
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := h) (g := π) x s₀ hs₀.symm
  let Ω : Type := AlgebraicClosure ((pullback h π).residueField w)
  let t : Sp Ω ⟶ pullback h π :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback h π).residueField w) Ω)) ≫
      (pullback h π).fromSpecResidueField w
  have ht : ∀ y, t y = w := by
    intro y
    simp only [t, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have hξ : ∀ y, (t ≫ pullback.fst h π) y = x := by
    intro y
    rw [Scheme.Hom.comp_apply, ht, hw]
  obtain ⟨p, hp, -⟩ := H Ω (t ≫ pullback.fst h π) (t ≫ pullback.snd h π)
    (by
      ext y
      constructor
      · rintro ⟨u, rfl⟩
        exact hξ u
      · rintro rfl
        exact ⟨closedPoint Ω, hξ _⟩)
    (by simp [pullback.condition])
  refine ⟨p (closedPoint Ω), ?_⟩
  have h₀ := hξ (closedPoint Ω)
  rw [← hp] at h₀
  exact (Scheme.Hom.comp_apply p a _).symm.trans h₀

end GlobalTheory.Mum
