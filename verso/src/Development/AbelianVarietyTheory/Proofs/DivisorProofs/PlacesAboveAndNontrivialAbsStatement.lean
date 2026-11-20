import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesAboveAndNontrivialAbs
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPlacesAboveAndNontrivialAbs.lean&line=140#L140)
-/
theorem _root_.GlobalTheory.T.places_above_and_nontrivial_abs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v) ∧ ∀ w : HeightOneSpectrum (𝓞 E), ∃ x : (w.adicCompletion E)ˣ, absE F E (locIdele F w x) ≠ 1 := by
  first | exact @GlobalTheory.PlaceAbove.places | exact GlobalTheory.PlaceAbove.places | (intros; apply GlobalTheory.PlaceAbove.places <;> assumption)
