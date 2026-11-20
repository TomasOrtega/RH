import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GramDetIndexSublattice
import Mathlib
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.gram_det_index_sublattice` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGramDetIndexSublattice.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.gram_det_eq_sq_mul_gram_det_of_mem_span : ∀ (U V ι κ : Type) [AddCommGroup U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (φ : U →ₗ[ℤ] V) (u : ι → U) (v : κ → U), Fintype.card ι = Fintype.card κ → (∀ k, v k ∈ Submodule.span ℤ (Set.range u)) → ∃ m : ℕ, (Matrix.gram ℝ fun k => φ (v k)).det = (m : ℝ) ^ 2 * (Matrix.gram ℝ fun i => φ (u i)).det ∧ ∀ i, (m : ℤ) • u i ∈ Submodule.span ℤ (Set.range v) := by
  first | exact @GlobalTheory.gram_det_index_sublattice | exact GlobalTheory.gram_det_index_sublattice | (intros; apply GlobalTheory.gram_det_index_sublattice <;> assumption)
