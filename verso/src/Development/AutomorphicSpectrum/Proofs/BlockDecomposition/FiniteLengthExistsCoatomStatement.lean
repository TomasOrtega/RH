import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthExistsCoatom
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FiniteLengthQuot.exists_isCoatom_subrepresentation` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteLengthExistsCoatom.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.finite_length_exists_coatom : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), HasFiniteLength ρ → Nontrivial V → ∃ S : Subrepresentation ρ, IsCoatom S := by
  first | exact @GlobalTheory.CompanionTheory.FiniteLengthQuot.exists_isCoatom_subrepresentation | exact GlobalTheory.CompanionTheory.FiniteLengthQuot.exists_isCoatom_subrepresentation | (intros; apply GlobalTheory.CompanionTheory.FiniteLengthQuot.exists_isCoatom_subrepresentation <;> assumption)
