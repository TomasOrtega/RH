import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureProdOfAddGroups
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FHaarMeasureProdOfAddGroups.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open : ∀ (V V' : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V] [AddCommGroup V'] [TopologicalSpace V'] [LocallyCompactSpace V'] [SecondCountableTopology V'] [T2Space V'] [MeasurableSpace V'] [BorelSpace V'] [IsTopologicalAddGroup V'] (μ : Measure V) [μ.IsAddHaarMeasure] (μ' : Measure V') [μ'.IsAddHaarMeasure] (e : V ≃+ V'), Continuous e → Continuous e.symm → (∃ a : ℝ≥0, a ≠ 0 ∧ μ.map e = a • μ') ∧ ∀ (L : Set V) (L' : Set V'), IsCompact L → IsOpen L → L.Nonempty → (∀ v, e v ∈ L' ↔ v ∈ L) → μ L = μ' L' → μ.map e = μ' := by
  first | exact @GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar | exact GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar | (intros; apply GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar <;> assumption)
