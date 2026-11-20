import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypSec

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))` using `FaithfulSMul.algebraMap_injective _ _`. Take `⟨Q, -, hQp, hQ⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E)) (Ideal.comap_bot_le_of_injective _ hinj)`. Establish `hQne : Q ≠ ⊥`. Introduce and unpack `rfl`. Apply `v.ne_bot` to reduce the goal to its premises.

Rewrite using `[← hQ]`. Conclude with `Ideal.comap_bot_of_injective _ hinj`. Conclude with `⟨⟨Q, hQp, hQne⟩, HeightOneSpectrum.ext hQ⟩`.
-/
private theorem exists_heightOneSpectrum_under_maximalRealSubfield {E : Type} [Field E] [NumberField E] [IsCMField E]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) = v := by
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (Ideal.comap_bot_le_of_injective _ hinj)
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQ]
    exact Ideal.comap_bot_of_injective _ hinj
  exact ⟨⟨Q, hQp, hQne⟩, HeightOneSpectrum.ext hQ⟩

/- English proof (translation)
Introduce `E _ _ _ S hS P hP`. Rewrite `hP`, the goal using `[Filter.eventually_cofinite]`. Use `(hP.image fun w : {w : Pl E // w ∈ S} => w.1.under (𝓞 (maximalRealSubfield E))).subset ?_` and prove the remaining obligations. Introduce `v hv`. Take `⟨w₀, hw₀⟩` from `exists_heightOneSpectrum_under_maximalRealSubfield v`.

Take `⟨u, ⟨huS, hu⟩, -⟩` from `hS w₀`. Conclude with `⟨⟨u, huS⟩, show ¬P (u.under _) by rw [hu, hw₀]; exact hv, hu.trans hw₀⟩`.
-/
theorem eventually_cofinite_of_section :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ P : PlF E → Prop,
  (∀ᶠ w : {w : Pl E // w ∈ S} in cofinite, P (w.1.under (𝓞 (maximalRealSubfield E)))) → ∀ᶠ v in cofinite, P v := by
  intro E _ _ _ S hS P hP
  rw [Filter.eventually_cofinite] at hP ⊢
  refine (hP.image fun w : {w : Pl E // w ∈ S} => w.1.under (𝓞 (maximalRealSubfield E))).subset ?_
  intro v hv
  obtain ⟨w₀, hw₀⟩ := exists_heightOneSpectrum_under_maximalRealSubfield v
  obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w₀
  exact ⟨⟨u, huS⟩, show ¬P (u.under _) by rw [hu, hw₀]; exact hv, hu.trans hw₀⟩

end GlobalTheory.CompanionTheory.LocHypSec
