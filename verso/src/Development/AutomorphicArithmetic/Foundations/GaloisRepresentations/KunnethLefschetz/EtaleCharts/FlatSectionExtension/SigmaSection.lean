import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Introduce `σ X f`. Set `L` to `isLimitOfPreserves (Scheme.Γ ⋙ forget CommRingCat) (coproductIsCoproduct X).op`. Set `e : Γ(∐ X, ⊤) ≃ ((Discrete.functor X).op ⋙ Scheme.Γ ⋙ forget CommRingCat).sections` to `Types.isLimitEquivSections L`. Establish `hproj : ∀ (s : Γ(∐ X, ⊤)) (p : σ), (e s).val (Opposite.op ⟨p⟩) = (Sigma.ι X p).appTop.hom s` using `fun s p => Types.isLimitEquivSections_apply L (Opposite.op ⟨p⟩) s`. Set `sec : ((Discrete.functor X).op ⋙ Scheme.Γ ⋙ forget CommRingCat).sections` to `⟨fun j => f j.unop.as, by`.

Introduce and unpack `⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨⟨h⟩⟩⟩`. Consider the cases of `h`. Use the proof step `rfl⟩`. Use `⟨e.symm sec, fun p => ?_, fun s' hs' => e.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← hproj, Equiv.apply_symm_apply]`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Take `⟨⟨q⟩⟩` from `j`. Rewrite using `[hproj, hs', Equiv.apply_symm_apply]`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaSection :
    ∀ {σ : Type} (X : σ → Scheme.{0}) (f : ∀ p, Γ(X p, ⊤)), ∃ s : Γ(∐ X, ⊤), (∀ p, (Sigma.ι X p).appTop.hom s = f p) ∧ ∀ s' : Γ(∐ X, ⊤), (∀ p, (Sigma.ι X p).appTop.hom s' = f p) → s' = s := by
  intro σ X f
  let L := isLimitOfPreserves (Scheme.Γ ⋙ forget CommRingCat) (coproductIsCoproduct X).op
  let e : Γ(∐ X, ⊤) ≃ ((Discrete.functor X).op ⋙ Scheme.Γ ⋙ forget CommRingCat).sections :=
    Types.isLimitEquivSections L
  have hproj : ∀ (s : Γ(∐ X, ⊤)) (p : σ), (e s).val (Opposite.op ⟨p⟩) = (Sigma.ι X p).appTop.hom s :=
    fun s p => Types.isLimitEquivSections_apply L (Opposite.op ⟨p⟩) s
  let sec : ((Discrete.functor X).op ⋙ Scheme.Γ ⋙ forget CommRingCat).sections :=
    ⟨fun j => f j.unop.as, by
      rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨⟨h⟩⟩⟩
      cases h
      rfl⟩
  refine ⟨e.symm sec, fun p => ?_, fun s' hs' => e.injective ?_⟩
  · rw [← hproj, Equiv.apply_symm_apply]
  · apply Subtype.ext
    funext j
    obtain ⟨⟨q⟩⟩ := j
    rw [hproj, hs', Equiv.apply_symm_apply]
