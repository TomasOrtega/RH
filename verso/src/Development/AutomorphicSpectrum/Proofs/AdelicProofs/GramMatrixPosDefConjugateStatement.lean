import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMatrixPosDefConjugate
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAdelicProofs%2FGramMatrixPosDefConjugate.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.gram_matrix_pos_def_conjugate : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (i : ℕ) (f : Fin i → B.carrier), LinearIndependent (𝓞 L) f → (∀ σ, (gramMat B σ f).PosDef) ∧ ∀ σ, gramMat B (ComplexEmbedding.conjugate σ) f = (gramMat B σ f).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.gramMat_posDef_and_conj | exact GlobalTheory.CompanionTheory.Ar.Lines.gramMat_posDef_and_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.gramMat_posDef_and_conj <;> assumption)
