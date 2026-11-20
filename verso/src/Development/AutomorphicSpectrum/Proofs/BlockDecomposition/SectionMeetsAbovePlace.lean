import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypAbove

/- English proof (translation)
Introduce `E _ _ _ S hS v`. Establish `hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))` using `FaithfulSMul.algebraMap_injective _ _`. Take `⟨Q, -, hQ, hQv⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E)) (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)`. Establish `hQ0 : Q ≠ ⊥`. Introduce and unpack `rfl`.

Rewrite `hQv` using `[Ideal.comap_bot_of_injective _ hinj]`. Conclude with `v.ne_bot hQv.symm`. Take `⟨u, ⟨hu, huw⟩, -⟩` from `hS (⟨Q, hQ, hQ0⟩ : Pl E)`. Conclude with `⟨⟨u, huw.trans (HeightOneSpectrum.ext hQv)⟩, hu⟩`.
-/
theorem exists_above_mem_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)),
    IsSection S → ∀ v : PlF E, ∃ w : Above v, w.1 ∈ S := by
  intro E _ _ _ S hS v
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    rw [Ideal.comap_bot_of_injective _ hinj] at hQv
    exact v.ne_bot hQv.symm
  obtain ⟨u, ⟨hu, huw⟩, -⟩ := hS (⟨Q, hQ, hQ0⟩ : Pl E)
  exact ⟨⟨u, huw.trans (HeightOneSpectrum.ext hQv)⟩, hu⟩

end GlobalTheory.CompanionTheory.LocHypAbove
