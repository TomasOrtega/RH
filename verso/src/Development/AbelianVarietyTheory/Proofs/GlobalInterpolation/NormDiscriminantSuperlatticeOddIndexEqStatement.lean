import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormDiscriminantSuperlatticeOddIndexEq
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FNormDiscriminantSuperlatticeOddIndexEq.lean&line=223#L223)
-/
theorem _root_.GlobalTheory.T.norm_discriminant_superlattice_odd_index_eq : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (L' : PeriodPair) (N : ℕ), q ≠ 2 → M.Ok → Nat.Coprime N (2 * q) → M.L.lattice ≤ L'.lattice → (∀ x ∈ L'.lattice, (N : ℂ) * x ∈ M.L.lattice) → ‖M.ι (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2)‖ = ‖M.ι (M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2)‖ := by
  first | exact @GlobalTheory.MomDisc.norm_disc_eq | exact GlobalTheory.MomDisc.norm_disc_eq | (intros; apply GlobalTheory.MomDisc.norm_disc_eq <;> assumption)
