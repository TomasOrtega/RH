import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageOverMaximalCompactResidue
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAverageOverMaximalCompactResidue.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.average_over_maximal_compact_residue : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ f : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ,
      avgK ϖ (fun κ => f (resK κ)) = sumG f / (Nat.card (GL (Ix n) (IsLocalRing.ResidueField O)) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.AvgRes.avgK_res | exact GlobalTheory.CompanionTheory.Jp.AvgRes.avgK_res | (intros; apply GlobalTheory.CompanionTheory.Jp.AvgRes.avgK_res <;> assumption)
