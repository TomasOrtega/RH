import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit

open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits

/- English proof (translation)
The claim follows from `inferInstanceAs (Subsingleton (PrimeSpectrum Ω))`.
-/
private lemma UpperTheory.Gal.LocalSmoothExtension.sp_subsingleton (Ω : Type) [Field Ω] : Subsingleton (UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))

/- English proof (translation)
Introduce `hF hSP hPS Y Z W s _ _ I _ c Δ _ σ hs`. Take `⟨hF1, hF2⟩` from `hF Y Z s I`. Take `⟨hsc, hiso⟩` from `hs`. Establish `hne : ∀ (Ω : Type) [Field Ω], Nonempty (UpperTheory.Gal.G3.sp Ω)` using `fun Ω _ => inferInstanceAs (Nonempty (PrimeSpectrum Ω))`. Establish `hpt : ∀ (Ω : Type) [Field Ω] (y : UpperTheory.Gal.G3.sp Ω ⟶ ∐ fun _ : I => Y), ∃ i : I, ∃ y' : UpperTheory.Gal.G3.sp Ω ⟶ Y, y' ≫ Sigma.ι (fun _ : I => Y) i = y`.

Introduce `Ω _ y`. Use `haveI := UpperTheory.Gal.LocalSmoothExtension.sp_subsingleton Ω`. Take `⟨p⟩` from `hne Ω`. Take `⟨⟨i, a⟩, ha⟩` from `(sigmaMk (fun _ : I => Y)).surjective (y.base p)`. Rewrite `ha` using `[sigmaMk_mk]`.

Use `⟨i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => Y) i) y ?_, IsOpenImmersion.lift_fac _ _ _⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `⟨a, by rw [Subsingleton.elim q p]; exact ha⟩`. Use `hSP _ c (I × Δ) _ ?_ ?_` and prove the remaining obligations. Introduce `z`.

Simplify using `[hsc]`. Introduce `Ω _ _ x y hy`. Take `⟨i, y', rfl⟩` from `hpt Ω y`. Establish `hy' : y' ≫ s = x ≫ c` using `by simpa using hy`. Take `⟨δ, hδ, hδu⟩` from `hPS s c Δ σ ⟨hsc, hiso⟩ Ω x y' hy'`.

Use `⟨(i, δ), ?_, ?_⟩` and prove the remaining obligations. Use `show x ≫ (σ δ ≫ _) = _`. Rewrite using `[← hδ, Category.assoc]`. Introduce and unpack `⟨i', δ'⟩ h`. Express the relevant statement in the definitionally equal form `x ≫ (σ δ' ≫ Sigma.ι (fun _ : I => Y) i') = y' ≫ Sigma.ι (fun _ : I => Y) i at h`.

Distinguish the cases in `hii : i' = i`. Substitute `hii` using the available equality. Establish `hx : x ≫ σ δ' = y'`. Rewrite `h` using `[← Category.assoc]`. Conclude with `(cancel_mono _).1 h`.

Rewrite using `[hδu δ' hx]`. Use `haveI := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : I => Y) (a := x ≫ σ δ') (b := y') ⟨by rw [Category.assoc]; exact h⟩ hii`. Take `⟨p⟩` from `hne Ω`. Conclude with `isEmptyElim p`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.sigmaSplit_of :
    SigmaFEt → UpperTheory.Gal.G3.SplitsPts → UpperTheory.Gal.G3.PtsOfSplits → SigmaSplit := by
  intro hF hSP hPS Y Z W s _ _ I _ c Δ _ σ hs
  obtain ⟨hF1, hF2⟩ := hF Y Z s I
  obtain ⟨hsc, hiso⟩ := hs
  have hne : ∀ (Ω : Type) [Field Ω], Nonempty (UpperTheory.Gal.G3.sp Ω) := fun Ω _ =>
    inferInstanceAs (Nonempty (PrimeSpectrum Ω))
  have hpt : ∀ (Ω : Type) [Field Ω] (y : UpperTheory.Gal.G3.sp Ω ⟶ ∐ fun _ : I => Y),
      ∃ i : I, ∃ y' : UpperTheory.Gal.G3.sp Ω ⟶ Y, y' ≫ Sigma.ι (fun _ : I => Y) i = y := by
    intro Ω _ y
    haveI := UpperTheory.Gal.LocalSmoothExtension.sp_subsingleton Ω
    obtain ⟨p⟩ := hne Ω
    obtain ⟨⟨i, a⟩, ha⟩ := (sigmaMk (fun _ : I => Y)).surjective (y.base p)
    rw [sigmaMk_mk] at ha
    refine ⟨i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => Y) i) y ?_,
      IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨q, rfl⟩
    exact ⟨a, by rw [Subsingleton.elim q p]; exact ha⟩
  refine hSP _ c (I × Δ) _ ?_ ?_
  · intro z
    simp [hsc]
  · intro Ω _ _ x y hy
    obtain ⟨i, y', rfl⟩ := hpt Ω y
    have hy' : y' ≫ s = x ≫ c := by simpa using hy
    obtain ⟨δ, hδ, hδu⟩ := hPS s c Δ σ ⟨hsc, hiso⟩ Ω x y' hy'
    refine ⟨(i, δ), ?_, ?_⟩
    · show x ≫ (σ δ ≫ _) = _
      rw [← hδ, Category.assoc]
    · rintro ⟨i', δ'⟩ h
      change x ≫ (σ δ' ≫ Sigma.ι (fun _ : I => Y) i') = y' ≫ Sigma.ι (fun _ : I => Y) i at h
      by_cases hii : i' = i
      · subst hii
        have hx : x ≫ σ δ' = y' := by
          rw [← Category.assoc] at h
          exact (cancel_mono _).1 h
        rw [hδu δ' hx]
      · haveI := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : I => Y) (a := x ≫ σ δ') (b := y')
          ⟨by rw [Category.assoc]; exact h⟩ hii
        obtain ⟨p⟩ := hne Ω
        exact isEmptyElim p
