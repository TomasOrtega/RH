import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedDvrAdjoiningUnitRoots
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_unramSub_of_pow_eq_units` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsUnramifiedDvrAdjoiningUnitRoots.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.exists_unramified_dvr_adjoining_unit_roots : ∀ (F : Type) [Field F] [IsAlgClosed F] (T : Subring F) [IsDiscreteValuationRing T] (k : ℕ), IsUnit (k : T) → ∀ U : Set Tˣ, U.Finite → ∃ T' : Subring F, GlobalTheory.UnramSub T.subtype T' ∧ ∀ x : F, (∃ u ∈ U, x ^ k = ((u : T) : F)) → x ∈ T' := by
  first | exact @GlobalTheory.exists_unramSub_of_pow_eq_units | exact GlobalTheory.exists_unramSub_of_pow_eq_units | (intros; apply GlobalTheory.exists_unramSub_of_pow_eq_units <;> assumption)
