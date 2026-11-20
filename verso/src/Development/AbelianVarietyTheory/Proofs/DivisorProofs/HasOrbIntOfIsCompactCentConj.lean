import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Introduce `H _ _ _ _ _ _ _ _ μ _ _ s hT dt _ _ hP y f hf hc`. Use `haveI : CompactSpace (cent s) := isCompact_iff_compactSpace.1 hT`. Take `⟨C, hC, h0⟩` from `hP _ hc`. Establish `hcont : Continuous (conjFn s f)` using `hf.comp (by fun_prop)`. Establish `hsupp : HasCompactSupport (conjFn s f)`.

Use `HasCompactSupport.intro' (hT.mul hC) (hT.mul hC).isClosed fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨t, ht, htx⟩` from `h0 x (subset_tsupport f hne)`. Conclude with `hx ⟨t⁻¹, (cent s).inv_mem ht, t * x, htx, by group⟩`. Establish `hint : Integrable (conjFn s f) μ` using `hcont.integrable_of_hasCompactSupport hsupp`.

Establish `e : (∫ x, f (x⁻¹ * (y⁻¹ * s * y) * x) ∂μ) = ∫ x, f (x⁻¹ * s * x) ∂μ`. Use `integral_mul_left_eq_self (μ := μ) (fun z => f (z⁻¹ * s * z)) y` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Use extensionality with `x`.

Use `congr 1`. Use `group`. Rewrite using `[e]`. Conclude with `hasOrbInt_of_finite hint`.
-/
theorem hasOrbInt_of_isCompact_cent_conj : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H), IsCompact (cent s : Set H) → ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant], IsProperOrbit (cent s) s → ∀ (y : H) (f : H → ℂ), Continuous f → HasCompactSupport f → HasOrbInt μ s dt f ((∫ x, f (x⁻¹ * (y⁻¹ * s * y) * x) ∂μ) / dt.real Set.univ) := by
  intro H _ _ _ _ _ _ _ _ μ _ _ s hT dt _ _ hP y f hf hc
  haveI : CompactSpace (cent s) := isCompact_iff_compactSpace.1 hT
  obtain ⟨C, hC, h0⟩ := hP _ hc
  have hcont : Continuous (conjFn s f) := hf.comp (by fun_prop)
  have hsupp : HasCompactSupport (conjFn s f) := by
    refine HasCompactSupport.intro' (hT.mul hC) (hT.mul hC).isClosed fun x hx => ?_
    by_contra hne
    obtain ⟨t, ht, htx⟩ := h0 x (subset_tsupport f hne)
    exact hx ⟨t⁻¹, (cent s).inv_mem ht, t * x, htx, by group⟩
  have hint : Integrable (conjFn s f) μ := hcont.integrable_of_hasCompactSupport hsupp
  have e : (∫ x, f (x⁻¹ * (y⁻¹ * s * y) * x) ∂μ) = ∫ x, f (x⁻¹ * s * x) ∂μ := by
    have := integral_mul_left_eq_self (μ := μ) (fun z => f (z⁻¹ * s * z)) y
    rw [← this]
    congr 1; ext x; congr 1; group
  rw [e]
  exact hasOrbInt_of_finite hint

end GlobalTheory
