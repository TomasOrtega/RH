import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IInfMapLeMapIInfOfFlat
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatIdealInf.iInf_map_le_map_iInf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIInfMapLeMapIInfOfFlat.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.iInf_map_le_map_iInf_of_flat : ∀ {B R : Type} [CommRing B] [CommRing R] [Algebra B R] [Module.Flat B R] {ι : Type} [Finite ι] (K : ι → Ideal B), ⨅ i, (K i).map (algebraMap B R) ≤ (⨅ i, K i).map (algebraMap B R) := by
  first | exact @GlobalTheory.FlatIdealInf.iInf_map_le_map_iInf | exact GlobalTheory.FlatIdealInf.iInf_map_le_map_iInf | (intros; apply GlobalTheory.FlatIdealInf.iInf_map_le_map_iInf <;> assumption)
