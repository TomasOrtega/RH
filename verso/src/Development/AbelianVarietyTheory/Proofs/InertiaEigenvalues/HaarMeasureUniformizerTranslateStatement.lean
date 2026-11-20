import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureUniformizerTranslate
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHaarMeasureUniformizerTranslate.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.haar_measure_uniformizer_translate : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ))
    (A : Set (GlobalTheory.CellDec.NA E n)), MeasurableSet A →
    ν {u : GlobalTheory.CellDec.NA E n | ∃ a ∈ A, (a : GA E n) = GlobalTheory.CellDec.tl n ϖ l * (u : GA E n) * (GlobalTheory.CellDec.tl n ϖ l)⁻¹} =
      ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ν A := by
  first | exact @GlobalTheory.CellDec.ModulusPf.modulus_conj | exact GlobalTheory.CellDec.ModulusPf.modulus_conj | (intros; apply GlobalTheory.CellDec.ModulusPf.modulus_conj <;> assumption)
