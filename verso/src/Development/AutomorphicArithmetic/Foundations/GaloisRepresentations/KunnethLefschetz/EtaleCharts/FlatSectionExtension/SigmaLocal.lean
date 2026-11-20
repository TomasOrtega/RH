import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaLocal :
    ∀ {σ : Type} (X : σ → Scheme.{0}) {V : Scheme.{0}} (a : V ⟶ ∐ X) (x : V), ∃ (U : V.Opens) (p : σ) (a₁ : (U : Scheme.{0}) ⟶ X p), x ∈ U ∧ U.ι ≫ a = a₁ ≫ Sigma.ι X p := by
  intro σ X V a x
  obtain ⟨⟨p, z⟩, hz⟩ := (sigmaMk X).surjective (a x)
  rw [sigmaMk_mk] at hz
  have hr : Set.range ((a ⁻¹ᵁ (Sigma.ι X p).opensRange).ι ≫ a) ⊆ Set.range (Sigma.ι X p) := by
    rintro _ ⟨y, rfl⟩
    exact y.2
  refine ⟨a ⁻¹ᵁ (Sigma.ι X p).opensRange, p,
    IsOpenImmersion.lift (Sigma.ι X p) ((a ⁻¹ᵁ (Sigma.ι X p).opensRange).ι ≫ a) hr, ?_, ?_⟩
  · show a x ∈ (Sigma.ι X p).opensRange
    exact ⟨z, hz⟩
  · exact (IsOpenImmersion.lift_fac _ _ _).symm
