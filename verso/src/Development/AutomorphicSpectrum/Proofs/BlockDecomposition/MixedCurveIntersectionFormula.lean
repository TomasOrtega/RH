import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartSingleton

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.MixZ

/- English proof (translation)
Introduce `Z _ q hq L M r hr`. Use `⟨fun σ => ?_, GlobalTheory.ArchDimZero.main ℤ Z q hq M L r hr⟩` and prove the remaining obligations. Use `GlobalTheory.ArchDimZero.isProper hq` as an intermediate fact. Use `GlobalTheory.ArchDimZero.finite_cxPts hq σ` as an intermediate fact. Establish `h₁ : (L.φ σ).chernPart 0 1 = Measure.count` using `Measure.ext_iff_singleton.2 fun y => by`.

Rewrite using `[GlobalTheory.ArchDimZero.chernPart_singleton hq L σ 1 y, Measure.count_singleton]`. Simplify using the standard rewrite rules. Establish `h₂ : (L.φ σ).chernPart 0 (-1) = 0` using `Measure.ext_iff_singleton.2 fun y => by`. Rewrite using `[GlobalTheory.ArchDimZero.chernPart_singleton hq L σ (-1) y]`. Simplify using the standard rewrite rules.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h₁]`. Conclude with `(Integrable.of_finite (μ := Measure.count) (f := logNorm (M.φ σ) r)).integrableOn`. Rewrite using `[h₂]`. Conclude with `(integrable_zero_measure : Integrable (logNorm (M.φ σ) r) 0).integrableOn`.
-/
theorem curveInt : CurveInt := by
  intro Z _ q hq L M r hr
  refine ⟨fun σ => ?_, GlobalTheory.ArchDimZero.main ℤ Z q hq M L r hr⟩
  have := GlobalTheory.ArchDimZero.isProper hq
  have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
  have h₁ : (L.φ σ).chernPart 0 1 = Measure.count := Measure.ext_iff_singleton.2 fun y => by
    rw [GlobalTheory.ArchDimZero.chernPart_singleton hq L σ 1 y, Measure.count_singleton]
    simp
  have h₂ : (L.φ σ).chernPart 0 (-1) = 0 := Measure.ext_iff_singleton.2 fun y => by
    rw [GlobalTheory.ArchDimZero.chernPart_singleton hq L σ (-1) y]
    simp
  refine ⟨?_, ?_⟩
  · rw [h₁]
    exact (Integrable.of_finite (μ := Measure.count) (f := logNorm (M.φ σ) r)).integrableOn
  · rw [h₂]
    exact (integrable_zero_measure : Integrable (logNorm (M.φ σ) r) 0).integrableOn

end GlobalTheory.CompanionTheory.MixZ
