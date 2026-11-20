import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormConjugateInverse
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspFormConjugateInverse.lean&line=256#L256)
-/
theorem _root_.GlobalTheory.T.cuspForm_conjugate_inverse : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}, ∀ (φ : Sm E a) (hψ : (fun g => star (φ.1 (invA E a g))) ∈ Sm E a), IsCuspForm φ → IsCuspForm (⟨fun g => star (φ.1 (invA E a g)), hψ⟩ : Sm E a) := by
  first | exact @GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA | exact GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA | (intros; apply GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA <;> assumption)
