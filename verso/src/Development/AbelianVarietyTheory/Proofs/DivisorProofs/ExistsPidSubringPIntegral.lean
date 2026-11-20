import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalizationAwayFromPrime
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem exists_pid_subring_pInt : ∀ (K : Type) [Field K] [CharZero K] (p : ℕ), p.Prime → ∀ s : Finset K,
    (∀ f ∈ s, IsIntegral ℤ f) → ∃ R : Subring K, IsPrincipalIdealRing R ∧ (∀ f ∈ s, f ∈ R) ∧ ∀ f ∈ R, PInt p f := by
  intro K _ _ p hp s hs
  let E := IntermediateField.adjoin ℚ (s : Set K)
  haveI : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_adjoin fun x hx =>
    (hs x hx).tower_top (A := ℚ)
  haveI : NumberField E := ⟨⟩
  obtain ⟨R', hR', hmem⟩ := GlobalTheory.exists_subring_pid_localization_coprime E p hp
  let φ : E →+* K := E.val.toRingHom
  have hφ : Function.Injective φ := φ.injective
  refine ⟨R'.map φ, ?_, ?_, ?_⟩
  · exact IsPrincipalIdealRing.of_surjective (R'.equivMapOfInjective φ hφ).toRingHom
      (R'.equivMapOfInjective φ hφ).surjective
  · intro f hf
    have hfE : f ∈ E := IntermediateField.subset_adjoin ℚ (s : Set K) hf
    refine ⟨⟨f, hfE⟩, (hmem _).2 ⟨1, Nat.coprime_one_left p, ?_⟩, rfl⟩
    rw [Nat.cast_one, one_mul]
    exact (isIntegral_algHom_iff (E.val.restrictScalars ℤ) hφ).1 (hs f hf)
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨r, hr, hi⟩ := (hmem y).1 hy
    refine ⟨r, hr, ?_⟩
    have := hi.map (E.val.restrictScalars ℤ)
    simpa [φ] using this

end GlobalTheory.LatChain
