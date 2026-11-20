import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScaledSkewLatticeFundamentalDomainOfImaginaryPar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SnMass.SkewDom.skewDom` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FScaledSkewLatticeFundamentalDomainOfImaginaryPar.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.scaledSkewLattice_fundamentalDomain_of_imaginaryParts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, σ x ∈ I) → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ (c : ℝ), 0 < c → ∀ (D : Set (InfinitePlace E → ℝ)) (m : ℝ≥0∞), MeasurableSet D → (∀ y, ∃! l, l ∈ {b | ∃ x ∈ I, imV x = b} ∧ y + l ∈ D) → volume D = m → HasDom volume (skewLat (σ : E →+* E) I c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal ((2 * c) ^ Fintype.card (InfinitePlace E)) * m) := by
  first | exact @GlobalTheory.SnMass.SkewDom.skewDom | exact GlobalTheory.SnMass.SkewDom.skewDom | (intros; apply GlobalTheory.SnMass.SkewDom.skewDom <;> assumption)
