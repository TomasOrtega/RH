import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlexanderWhitneyDiagonalSwapHomotopy
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsAlexanderWhitneyDiagonalSwapHomotopy.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.exists_alexanderWhitneyDiagonal_swap_homotopy : ∃ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧ ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  first | exact @GlobalTheory.EtC.pr_aw_wa_homotopy | exact GlobalTheory.EtC.pr_aw_wa_homotopy | (intros; apply GlobalTheory.EtC.pr_aw_wa_homotopy <;> assumption)
