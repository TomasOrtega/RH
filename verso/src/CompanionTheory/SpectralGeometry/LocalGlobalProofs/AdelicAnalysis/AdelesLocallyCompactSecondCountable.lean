import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdeleTop

/- English proof (translation)
The claim follows from `inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))`.
-/
theorem t2Space_finiteAdeleRing_of_numberField (F : Type) [Field F] [NumberField F] : T2Space (Af F) :=
  inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))

/- English proof (translation)
The claim follows from `inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))`.
-/
theorem t2Space_infiniteAdeleRing_of_numberField_field (F : Type) [Field F] [NumberField F] : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

/- English proof (translation)
Introduce `F _ _`. Use `⟨⟨GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F, GlobalTheory.AdelicUnitaryTop.secondCountable_adele F, ?_⟩, GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F, GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F, t2Space_finiteAdeleRing_of_numberField F⟩` and prove the remaining obligations. Use `haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := t2Space_finiteAdeleRing_of_numberField F`. Use `haveI := t2Space_infiniteAdeleRing_of_numberField_field F`. Conclude with `inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))`.
-/
theorem adele_top : ∀ (F : Type) [Field F] [NumberField F],
    (LocallyCompactSpace (AF F) ∧ SecondCountableTopology (AF F) ∧ T2Space (AF F)) ∧
    (LocallyCompactSpace (Af F) ∧ SecondCountableTopology (Af F) ∧ T2Space (Af F)) := by
  intro F _ _
  refine ⟨⟨GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F,
    GlobalTheory.AdelicUnitaryTop.secondCountable_adele F, ?_⟩,
    GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F,
    GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F, t2Space_finiteAdeleRing_of_numberField F⟩
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := t2Space_finiteAdeleRing_of_numberField F
  haveI := t2Space_infiniteAdeleRing_of_numberField_field F
  exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end GlobalTheory.CompanionTheory.AdeleTop
