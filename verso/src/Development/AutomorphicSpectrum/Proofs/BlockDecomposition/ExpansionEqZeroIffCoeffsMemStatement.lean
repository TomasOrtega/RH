import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionEqZeroIffCoeffsMem
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ExpandKer.expand_eq_zero_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExpansionEqZeroIffCoeffsMem.lean&line=189#L189)
-/
theorem _root_.GlobalTheory.T.expansion_eq_zero_iff_coeffs_mem : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (c : ℕ →₀ A.A), A.expand c = 0 ↔ ∀ k, c k ∈ Ideal.span {A.pi ^ l} := by
  first | exact @GlobalTheory.CompanionTheory.ExpandKer.expand_eq_zero_iff | exact GlobalTheory.CompanionTheory.ExpandKer.expand_eq_zero_iff | (intros; apply GlobalTheory.CompanionTheory.ExpandKer.expand_eq_zero_iff <;> assumption)
