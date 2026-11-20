import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumNormSqOrthonormalLeHilbertSchmidtStatement
open Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Set `b` to `stdOrthonormalBasis ℂ N`. Set `v : Fin (Module.finrank ℂ N) → V` to `fun i => (b i : V)`. Apply the tactic sequence `have hv : Orthonormal ℂ v := b.orthonormal.comp_linearIsometry N.subtypeₗᵢ`. Establish `h` using `GlobalTheory.T.sum_norm_sq_orthonormal_le_hilbertSchmidt (K - ContinuousLinearMap.id ℂ V) v hv`. Establish `hterm : ∀ i, ‖(K - ContinuousLinearMap.id ℂ V) (v i)‖ ^ 2 = 1`.

Introduce `i`. Establish `hK : K (v i) = 0` using `hN _ (b i).2`. Establish `hn : ‖v i‖ = 1` using `hv.1 i`. Simplify using `[hK, hn]`. Establish `hsum : ∑ i, ‖(K - ContinuousLinearMap.id ℂ V) (v i)‖ ^ 2 = (Module.finrank ℂ N : ℝ)`.

Rewrite using `[Finset.sum_congr rfl (fun i _ => hterm i)]`. Simplify using the standard rewrite rules. Rewrite `h` using `[hsum]`. Conclude with `h`.
-/
theorem finrank_ker_le_hsNormSq_sub_id {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (K : V →L[ℂ] V) (N : Submodule ℂ V) (hN : ∀ x ∈ N, K x = 0) :
    (Module.finrank ℂ N : ℝ) ≤ hsNormSq (K - ContinuousLinearMap.id ℂ V) := by
  let b := stdOrthonormalBasis ℂ N
  let v : Fin (Module.finrank ℂ N) → V := fun i => (b i : V)
  have hv : Orthonormal ℂ v := b.orthonormal.comp_linearIsometry N.subtypeₗᵢ
  have h := GlobalTheory.T.sum_norm_sq_orthonormal_le_hilbertSchmidt (K - ContinuousLinearMap.id ℂ V) v hv
  have hterm : ∀ i, ‖(K - ContinuousLinearMap.id ℂ V) (v i)‖ ^ 2 = 1 := by
    intro i
    have hK : K (v i) = 0 := hN _ (b i).2
    have hn : ‖v i‖ = 1 := hv.1 i
    simp [hK, hn]
  have hsum : ∑ i, ‖(K - ContinuousLinearMap.id ℂ V) (v i)‖ ^ 2 = (Module.finrank ℂ N : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    simp
  rw [hsum] at h
  exact h

end GlobalTheory
