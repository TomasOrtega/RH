import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AddHaarMapSmulOfNormEqOne
import Mathlib
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FAddHaarMapSmulOfNormEqOne.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.map_smul_addHaar_of_norm_eq_one : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (c : K), ‖c‖ = 1 → Measure.map (fun x : V => c • x) μ = μ := by
  first | exact @GlobalTheory.addHaar_map_smul_of_norm_eq_one | exact GlobalTheory.addHaar_map_smul_of_norm_eq_one | (intros; apply GlobalTheory.addHaar_map_smul_of_norm_eq_one <;> assumption)
