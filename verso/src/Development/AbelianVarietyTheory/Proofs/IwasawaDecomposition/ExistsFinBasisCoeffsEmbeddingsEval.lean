import Mathlib

open NumberField

namespace GlobalTheory

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem embeddings_eval_onto (L : Type) [Field L] [NumberField L] (K : Type) [Field K] [CharZero K]
    (z : (L →+* K) → K) :
    ∃ y : Fin (Module.finrank ℚ L) → K, ∀ σ : L →+* K,
      ∑ i, σ (Module.finBasis ℚ L i) * y i = z σ := by
  classical
  set b := Module.finBasis ℚ L
  let M : Matrix (L →+* K) (Fin (Module.finrank ℚ L)) K := Matrix.of fun σ i => σ (b i)

  have hD : LinearIndependent K (fun σ : L →+* K => (σ : L → K)) := by
    have h := linearIndependent_monoidHom L K
    have hinj : Function.Injective (fun σ : L →+* K => (σ.toMonoidHom : L →* K)) := by
      intro σ τ h'
      ext x
      exact DFunLike.congr_fun h' x
    exact h.comp _ hinj
  have hrow : LinearIndependent K M.row := by
    rw [Fintype.linearIndependent_iff] at hD ⊢
    intro g hg
    apply hD g
    have hb : ∀ i, ∑ σ, g σ * σ (b i) = 0 := by
      intro i
      have := congr_fun hg i
      simpa [M, Matrix.row, Finset.sum_apply] using this
    funext x
    rw [← b.sum_repr x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, map_sum]
    have : ∀ σ : L →+* K, ∀ i, σ (b.repr x i • b i) = (b.repr x i : K) * σ (b i) := by
      intro σ i
      rw [Algebra.smul_def, map_mul]
      simp
    simp_rw [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h2 : ∑ σ : L →+* K, g σ * ((b.repr x i : K) * σ (b i)) =
        (b.repr x i : K) * ∑ σ : L →+* K, g σ * σ (b i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [h2, hb i, mul_zero]
  have hrank : M.rank = Fintype.card (L →+* K) := hrow.rank_matrix
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hrank, Module.finrank_fintype_fun_eq_card]
  have hz : z ∈ LinearMap.range M.mulVecLin := by rw [htop]; trivial
  obtain ⟨y, hy⟩ := hz
  refine ⟨y, fun σ => ?_⟩
  have := congr_fun hy σ
  simpa [M, Matrix.mulVec, dotProduct] using this

end GlobalTheory
