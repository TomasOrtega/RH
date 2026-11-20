import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueUpperUnipotentLift
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FResidueUpperUnipotentLift.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.residue_upper_unipotent_lift : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ x : GL (Ix n) (IsLocalRing.ResidueField O), x.1.toBlocks₁₂ = 0 →
      ∃ j j' : GL (Ix n) O, inL j * tauM w = tauM w * inL j' ∧ resK j' = x := by
  first | exact @GlobalTheory.CompanionTheory.Jp.twist_low | exact GlobalTheory.CompanionTheory.Jp.twist_low | (intros; apply GlobalTheory.CompanionTheory.Jp.twist_low <;> assumption)
