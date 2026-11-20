import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionCorankEqRankLowerLeft
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Jp.RedRank.iD_eq_rank` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FReductionCorankEqRankLowerLeft.lean&line=116#L116)
-/
theorem _root_.GlobalTheory.T.reduction_corank_eq_rank_lower_left : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ (κ : GL (Ix n) O) (h : GL (Ix n) (IsLocalRing.ResidueField O)), IsRed (O := O) w κ h →
      iD h = (lowerLeftBlock (resK κ)).rank := by
  first | exact @GlobalTheory.CompanionTheory.Jp.RedRank.iD_eq_rank | exact GlobalTheory.CompanionTheory.Jp.RedRank.iD_eq_rank | (intros; apply GlobalTheory.CompanionTheory.Jp.RedRank.iD_eq_rank <;> assumption)
