import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatThickeningQuotient
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFlatThickeningQuotient.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.flat_thickening_quotient : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O] (F : B.Fn O) (ρ : O →+* k) (n : ℕ) (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))), FlatT T → FlatT (qT hn T) := by
  first | exact @GlobalTheory.CompanionTheory.FlatThick.flatT_qT | exact GlobalTheory.CompanionTheory.FlatThick.flatT_qT | (intros; apply GlobalTheory.CompanionTheory.FlatThick.flatT_qT <;> assumption)
