import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyDiagonalAndSwapChainMaps
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtC.AWChain.aw_wa_chain` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAlexanderWhitneyDiagonalAndSwapChainMaps.lean&line=146#L146)
-/
theorem _root_.GlobalTheory.T.alexanderWhitneyDiagonal_and_swap_chain_maps : ∀ N, Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N) ∧ Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N) := by
  first | exact @GlobalTheory.EtC.AWChain.aw_wa_chain | exact GlobalTheory.EtC.AWChain.aw_wa_chain | (intros; apply GlobalTheory.EtC.AWChain.aw_wa_chain <;> assumption)
