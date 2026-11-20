import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIdempotentComplementIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMemIdempotentComplementIff.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.mem_idempotent_complement_iff : ∀ {S : Type} [CommRing S] (P : Ideal S), P.IsPrime → ∀ x : S, x ∈ compI P ↔ ∃ e, IsIdempotentElem e ∧ e ∉ P ∧ e * x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff | exact GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff | (intros; apply GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff <;> assumption)
