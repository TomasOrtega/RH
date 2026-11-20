import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FVectorTupleProductMeasureTwoSidedAction.lean&line=168#L168)
-/
theorem _root_.GlobalTheory.T.vectorTupleProductMeasure_two_sided_action : ∀ (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S], IsArtinianRing S → IsReduced S → ∀ (lam : Measure S), lam.IsAddHaarMeasure → ∀ (n M : ℕ) (g : Matrix (Fin M) (Fin M) S) (γ : Matrix (Fin n) (Fin n) S), IsUnit g.det → IsUnit γ.det → tupMeas lam n M = (modu S g.det ^ n * modu S γ.det ^ M) • (tupMeas lam n M).map (lrAct g γ) := by
  first | exact @GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct | exact GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct | (intros; apply GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct <;> assumption)
