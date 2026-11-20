import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixComponentAtPlaceMemCompletedLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FWeilMatrixComponentAtPlaceMemCompletedLattice.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : FinPl D → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT P → ∀ p : Place D, wAt p u ∈ (latO S T ΛS ΛT fun v => P v ∧ Sum.inl v = p) ∧ u - wAt p u ∈ (latO S T ΛS ΛT fun v => P v ∧ Sum.inl v ≠ p) ∧ ((∀ v, P v → Sum.inl v ≠ p) → wAt p u = 0) := by
  first | exact @GlobalTheory.LatticeLocal.wAt_mem_latO | exact GlobalTheory.LatticeLocal.wAt_mem_latO | (intros; apply GlobalTheory.LatticeLocal.wAt_mem_latO <;> assumption)
