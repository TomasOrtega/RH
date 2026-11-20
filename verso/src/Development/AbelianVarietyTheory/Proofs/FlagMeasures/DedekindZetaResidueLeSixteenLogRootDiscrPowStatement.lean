import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DedekindZetaResidueLeSixteenLogRootDiscrPow
import Formalism.HermitianLattices.StatementMass
open MeasureTheory NumberField Finset
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FDedekindZetaResidueLeSixteenLogRootDiscrPow.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.dedekindZeta_residue_le_sixteen_log_rootDiscr_pow : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → 0 < dedekindZeta_residue K ∧ dedekindZeta_residue K ≤ (16 * Real.log (2 * Formalism.HermitianLatticesTheory.vInv K)) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
  first | exact @GlobalTheory.dedekindZeta_residue_le_log_rootDiscr_pow | exact GlobalTheory.dedekindZeta_residue_le_log_rootDiscr_pow | (intros; apply GlobalTheory.dedekindZeta_residue_le_log_rootDiscr_pow <;> assumption)
