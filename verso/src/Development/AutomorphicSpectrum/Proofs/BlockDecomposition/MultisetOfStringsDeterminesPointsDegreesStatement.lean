import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetOfStringsDeterminesPointsDegrees
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.StringsTwo
open GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMultisetOfStringsDeterminesPointsDegrees.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.multiset_of_strings_determines_points_degrees : ∀ {X ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → X) (d : ι → ℕ) (p' : κ → X) (d' : κ → ℕ), (∀ i, 1 ≤ d i) → (∀ j, 1 ≤ d' j) → GlobalTheory.Rigid.strings p d = GlobalTheory.Rigid.strings p' d' → ∃ s : ι ≃ κ, ∀ i, p i = p' (s i) ∧ d i = d' (s i) := by
  first | exact @GlobalTheory.CompanionTheory.Rigid.strings_rigid | exact GlobalTheory.CompanionTheory.Rigid.strings_rigid | (intros; apply GlobalTheory.CompanionTheory.Rigid.strings_rigid <;> assumption)
