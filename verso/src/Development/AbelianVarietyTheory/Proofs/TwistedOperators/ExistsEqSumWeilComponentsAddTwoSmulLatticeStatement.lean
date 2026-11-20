import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqSumWeilComponentsAddTwoSmulLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsEqSumWeilComponentsAddTwoSmulLattice.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : WO S T, ∃ P₀ : Finset (Place D), ∀ P : Finset (Place D), P₀ ⊆ P → ∃ u ∈ (latO S T ΛS ΛT fun _ => True), w = ∑ p ∈ P, wAt p w + 2 • u := by
  first | exact @GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul | exact GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul | (intros; apply GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul <;> assumption)
