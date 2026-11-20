import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit

open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits

/- English proof (translation)
A detailed English derivation is pending.
-/
private lemma UpperTheory.Gal.LocalSmoothExtension.sp_subsingleton (Ω : Type) [Field Ω] : Subsingleton (UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
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
