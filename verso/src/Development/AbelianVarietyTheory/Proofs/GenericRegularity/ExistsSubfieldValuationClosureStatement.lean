import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSubfieldValuationClosure
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import ReciprocityTheory.SemistableReduction.AlgAll
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_subfield_valuation_closure` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGenericRegularity%2FExistsSubfieldValuationClosure.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_subfield_valuation_closure' : ∀ (U : Type) [Field U] (v : Valuation U (WithZero (Multiplicative ℤ))) (S : Subfield U), ∃ S' : Subfield U, ∀ u, u ∈ S' ↔ ∀ γ : WithZero (Multiplicative ℤ), γ ≠ 0 → ∃ s ∈ S, v (u - s) < γ := by
  first | exact @GlobalTheory.exists_subfield_valuation_closure | exact GlobalTheory.exists_subfield_valuation_closure | (intros; apply GlobalTheory.exists_subfield_valuation_closure <;> assumption)
