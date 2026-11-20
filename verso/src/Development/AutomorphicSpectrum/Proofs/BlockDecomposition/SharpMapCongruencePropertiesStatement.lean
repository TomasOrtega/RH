import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpMapCongruenceProperties
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Untilt.sharp_congruences` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSharpMapCongruenceProperties.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.sharp_map_congruence_properties : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), (∀ (a b : A.A) (n : ℕ), a - b ∈ Ideal.span {A.pi} → A.sharp (a ^ l ^ n) - A.sharp (b ^ l ^ n) ∈ Ideal.span {(l : A.U) ^ (n + 1)}) ∧ (∀ a b : A.A, A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} ↔ a - b ∈ Ideal.span {A.pi}) ∧ ∀ e : A.A, IsIdempotentElem e → A.sharp (1 - e) = 1 - A.sharp e := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.sharp_congruences | exact GlobalTheory.CompanionTheory.Untilt.sharp_congruences | (intros; apply GlobalTheory.CompanionTheory.Untilt.sharp_congruences <;> assumption)
