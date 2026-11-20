import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorMemLowSpanSupVerma
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeightVectorMemLowSpanSupVerma.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.weight_vector_mem_low_span_sup_verma : ∀ {n : ℕ} (μ : Fin n → ℤ) (x : U n), IsAdW μ x → x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n) := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW | exact GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW | (intros; apply GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW <;> assumption)
