import Mathlib

open AlgebraicGeometry CategoryTheory Limits

/- English proof (translation)
Introduce `I Z K _`. Take `⟨z⟩ : Nonempty (Spec (CommRingCat.of K))` from `inferInstance`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, f⟩ ⟨c', f'⟩ h`. Simplify using `only at h`.

Establish `hz : (Sigma.ι Z c) (f z) = (Sigma.ι Z c') (f' z)`. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]`. Establish `hs` using `(sigmaι_eq_iff Z c c' (f z) (f' z)).mp hz`. Take `⟨rfl, -⟩` from `Sigma.mk.inj hs`. Establish `hff : f = f'` using `(cancel_mono (Sigma.ι Z c)).mp h`.

Rewrite using `[hff]`. Introduce `f`. Take `⟨⟨c, y⟩, hy⟩` from `(sigmaMk Z).surjective (f z)`. Rewrite `hy` using `[sigmaMk_mk]`. Establish `H : Set.range f ⊆ Set.range (Sigma.ι Z c)`.

Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `⟨y, by rw [hy, Subsingleton.elim w z]⟩`. Conclude with `⟨⟨c, IsOpenImmersion.lift (Sigma.ι Z c) f H⟩, IsOpenImmersion.lift_fac _ _ _⟩`.
-/
theorem UpperTheory.bijective_sigma_spec_points_coproduct :
    ∀ {I : Type} (Z : I → Scheme.{0}) (K : Type) [Field K], Function.Bijective (fun p : (Σ c, (Spec (CommRingCat.of K) ⟶ Z c)) => p.2 ≫ Sigma.ι Z p.1) := by
  intro I Z K _
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  constructor
  · rintro ⟨c, f⟩ ⟨c', f'⟩ h
    simp only at h
    have hz : (Sigma.ι Z c) (f z) = (Sigma.ι Z c') (f' z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
    have hs := (sigmaι_eq_iff Z c c' (f z) (f' z)).mp hz
    obtain ⟨rfl, -⟩ := Sigma.mk.inj hs
    have hff : f = f' := (cancel_mono (Sigma.ι Z c)).mp h
    rw [hff]
  · intro f
    obtain ⟨⟨c, y⟩, hy⟩ := (sigmaMk Z).surjective (f z)
    rw [sigmaMk_mk] at hy
    have H : Set.range f ⊆ Set.range (Sigma.ι Z c) := by
      rintro _ ⟨w, rfl⟩
      exact ⟨y, by rw [hy, Subsingleton.elim w z]⟩
    exact ⟨⟨c, IsOpenImmersion.lift (Sigma.ι Z c) f H⟩, IsOpenImmersion.lift_fac _ _ _⟩
