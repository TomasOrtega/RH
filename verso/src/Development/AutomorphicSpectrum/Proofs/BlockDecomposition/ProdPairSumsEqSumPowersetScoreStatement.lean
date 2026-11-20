import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdPairSumsEqSumPowersetScore
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FProdPairSumsEqSumPowersetScore.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.prod_pair_sums_eq_sum_powerset_score : ∀ {n : ℕ} (z : Fin n → ℂ), ∏ p ∈ prs n, (z p.1 + z p.2) = ∑ T ∈ (prs n).powerset, ∏ a, z a ^ score T a := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.prod_pairs_add_eq_sum_score | exact GlobalTheory.CompanionTheory.CoefId.prod_pairs_add_eq_sum_score | (intros; apply GlobalTheory.CompanionTheory.CoefId.prod_pairs_add_eq_sum_score <;> assumption)
