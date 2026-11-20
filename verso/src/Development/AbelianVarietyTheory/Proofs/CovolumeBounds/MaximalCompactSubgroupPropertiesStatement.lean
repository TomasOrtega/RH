import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MaximalCompactSubgroupProperties
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HCXi.KGroup.kset_facts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCovolumeBounds%2FMaximalCompactSubgroupProperties.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.maximal_compact_subgroup_properties : ∀ k r : ℕ, IsClosedSubgroup (Kset k r) ∧ IsCompact (Kset k r) ∧ Hpk k r ∈ Kset k r ∧ (∀ κ ∈ Kset k r, κᴴ ∈ Kset k r ∧ κ * Hpk k r = Hpk k r * κ) ∧ ∀ κ ∈ Kset k r, ∀ κ' ∈ Kset k r, ∀ g : Mat k r, gN (κ * g * κ') = gN g := by
  first | exact @GlobalTheory.HCXi.KGroup.kset_facts | exact GlobalTheory.HCXi.KGroup.kset_facts | (intros; apply GlobalTheory.HCXi.KGroup.kset_facts <;> assumption)
