import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClosedEmbeddingOfCongruenceSubgroupsConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsClosedEmbeddingOfCongruenceSubgroupsConj.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.isClosedEmbedding_of_congruenceSubgroups_conj : ∀ (I I' : AutInst) (j : I'.Gf →* I.Gf) (xf : I.Gf), (∀ (N : ℕ) (g : I'.Gf), g ∈ I'.Kg N ↔ xf⁻¹ * j g * xf ∈ I.Kg N) → Topology.IsClosedEmbedding j := by
  first | exact @GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg | exact GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg | (intros; apply GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg <;> assumption)
