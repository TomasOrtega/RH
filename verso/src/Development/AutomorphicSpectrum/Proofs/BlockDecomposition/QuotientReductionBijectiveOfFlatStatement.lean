import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientReductionBijectiveOfFlat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.QredFlat.qred_bij` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FQuotientReductionBijectiveOfFlat.lean&line=259#L259)
-/
theorem _root_.GlobalTheory.T.quotient_reduction_bijective_of_flat : ∀ (W : Type) [CommRing W] (l : ℕ) (K L : Cx.{1} W) (m : ℕ) (f : Cx.Hom K (quo l L m) (RingHom.id W)), FlatL l m K → FlatL l (m + 1) L → (∀ j, Function.Bijective (f.mapH j)) → ∀ b (h : b ≤ m) j, Function.Bijective ((qred l f h).mapH j) := by
  first | exact @GlobalTheory.CompanionTheory.QredFlat.qred_bij | exact GlobalTheory.CompanionTheory.QredFlat.qred_bij | (intros; apply GlobalTheory.CompanionTheory.QredFlat.qred_bij <;> assumption)
