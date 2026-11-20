import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepUnitaryTwistExists
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCuspRepUnitaryTwistExists.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.cusp_rep_unitary_twist_exists : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CG E a), 1 ≤ a →
    ∃ ν : Formalism.L2.Host.HChar E, (∀ w, ν.UnrAt w) ∧ (π.twist ν).IsUnitary := by
  first | exact @GlobalTheory.CuspRep.exists_unramified_twist_isUnitary | exact GlobalTheory.CuspRep.exists_unramified_twist_isUnitary | (intros; apply GlobalTheory.CuspRep.exists_unramified_twist_isUnitary <;> assumption)
