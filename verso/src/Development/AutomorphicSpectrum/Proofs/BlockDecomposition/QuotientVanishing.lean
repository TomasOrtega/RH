import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBasisDiagonalTwistedCentralizerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjCompactOfDiagonalNilradicalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralUnfoldWeightedAverageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilradicalTranslationMeasurePreservingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjTwistedCentralizerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsWeightNilradicalIntegralOneStatement

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

/- English proof (translation)
Introduce `n _ _ μ _ d μd _ W₁ W₂ hsep hW0 hW hp1 hp2 F hF hFT _ hvan`. Use `haveI := locallyCompact_GL n`. Use `haveI := secondCountable_GL n`. Use `haveI := sigmaFinite_twCent d μd`. Take `⟨P, hdiag, hzero, himg⟩` from `GlobalTheory.T.exists_basis_diagonal_twisted_centralizer n d W₁ W₂ hsep hW hp1 hp2`.

Establish `hc : ∀ a ∈ twCent (thC n) d, ∀ b ∈ twCent (thC n) d, a * b = b * a`. Introduce `a ha b hb`. Take `⟨x, hx⟩` from `hdiag a ha`. Take `⟨y, hy⟩` from `hdiag b hb`. Establish `e : (P⁻¹ * a * P) * (P⁻¹ * b * P) = (P⁻¹ * b * P) * (P⁻¹ * a * P)` using `Units.ext (by`.

Rewrite using `[Units.val_mul (P⁻¹ * a * P), Units.val_mul (P⁻¹ * b * P), hx, hy, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `mul_comm _ _)`. Establish `e2 : P⁻¹ * (a * b) * P = P⁻¹ * (b * a) * P`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_left_cancel (mul_right_cancel e2)`. Use `haveI := invInvariant_twCent d μd hc`. Establish `hnorm : ∀ t ∈ twCent (thC n) d, ∀ X ∈ nilrad W₁ W₂, t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂`. Introduce `t ht X hX`.

Use `conj_mem t hX` as an intermediate fact. Rewrite `this` using `[(himg t ht).1, (himg t ht).2]`. Then use the resulting hypothesis. Take `⟨ρ, hρ, hρN⟩` from `GlobalTheory.T.compact_conj_twisted_centralizer n d μd W₁ W₂ hW hc hnorm (GlobalTheory.T.conj_compact_of_diagonal_nilradical n d μd W₁ W₂ P hW hdiag hzero)`. Rewrite using `[GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hF hFT hρ]`. Use `letI : MeasurableSpace (nilrad W₁ W₂) := borel _`.

Use `haveI : BorelSpace (nilrad W₁ W₂) := ⟨rfl⟩`. Use `haveI := locallyCompact_nilrad W₁ W₂`. Use `haveI := secondCountable_nilrad W₁ W₂`. Set `ν : Measure (nilrad W₁ W₂)` to `Measure.addHaar`. Use `haveI : ν.IsAddHaarMeasure := by dsimp only [ν]; infer_instance`.

Take `⟨w, hwm, hw⟩` from `GlobalTheory.T.exists_weight_nilradical_integral_one n W₁ W₂ hW ν (fun Y => GlobalTheory.T.nilradical_translation_measure_preserving n W₁ W₂ hW ν Y)`. Conclude with `GlobalTheory.T.integral_unfold_weighted_average μ ν uOf continuous_uOf.measurable w ρ F hwm hρ.1 hF hw hρN (fun q => hvan ν q)`.
-/
theorem quotVanish : QuotVanish := by
  intro n _ _ μ _ d μd _ W₁ W₂ hsep hW0 hW hp1 hp2 F hF hFT _ hvan
  haveI := locallyCompact_GL n
  haveI := secondCountable_GL n
  haveI := sigmaFinite_twCent d μd
  obtain ⟨P, hdiag, hzero, himg⟩ := GlobalTheory.T.exists_basis_diagonal_twisted_centralizer n d W₁ W₂ hsep hW hp1 hp2
  have hc : ∀ a ∈ twCent (thC n) d, ∀ b ∈ twCent (thC n) d, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx⟩ := hdiag a ha
    obtain ⟨y, hy⟩ := hdiag b hb
    have e : (P⁻¹ * a * P) * (P⁻¹ * b * P) = (P⁻¹ * b * P) * (P⁻¹ * a * P) :=
      Units.ext (by
        rw [Units.val_mul (P⁻¹ * a * P), Units.val_mul (P⁻¹ * b * P), hx, hy, Matrix.diagonal_mul_diagonal,
          Matrix.diagonal_mul_diagonal]
        congr 1; funext i; exact mul_comm _ _)
    have e2 : P⁻¹ * (a * b) * P = P⁻¹ * (b * a) * P := by
      calc P⁻¹ * (a * b) * P = (P⁻¹ * a * P) * (P⁻¹ * b * P) := by group
        _ = (P⁻¹ * b * P) * (P⁻¹ * a * P) := e
        _ = P⁻¹ * (b * a) * P := by group
    exact mul_left_cancel (mul_right_cancel e2)
  haveI := invInvariant_twCent d μd hc
  have hnorm : ∀ t ∈ twCent (thC n) d, ∀ X ∈ nilrad W₁ W₂,
      t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂ := by
    intro t ht X hX
    have := conj_mem t hX
    rwa [(himg t ht).1, (himg t ht).2] at this
  obtain ⟨ρ, hρ, hρN⟩ := GlobalTheory.T.compact_conj_twisted_centralizer n d μd W₁ W₂ hW hc hnorm
    (GlobalTheory.T.conj_compact_of_diagonal_nilradical n d μd W₁ W₂ P hW hdiag hzero)
  rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hF hFT hρ]
  letI : MeasurableSpace (nilrad W₁ W₂) := borel _
  haveI : BorelSpace (nilrad W₁ W₂) := ⟨rfl⟩
  haveI := locallyCompact_nilrad W₁ W₂
  haveI := secondCountable_nilrad W₁ W₂
  let ν : Measure (nilrad W₁ W₂) := Measure.addHaar
  haveI : ν.IsAddHaarMeasure := by dsimp only [ν]; infer_instance
  obtain ⟨w, hwm, hw⟩ := GlobalTheory.T.exists_weight_nilradical_integral_one n W₁ W₂ hW ν (fun Y => GlobalTheory.T.nilradical_translation_measure_preserving n W₁ W₂ hW ν Y)
  exact GlobalTheory.T.integral_unfold_weighted_average μ ν uOf continuous_uOf.measurable w ρ F hwm hρ.1 hF hw hρN (fun q => hvan ν q)

end GlobalTheory.CompanionTheory.LocVan
end
