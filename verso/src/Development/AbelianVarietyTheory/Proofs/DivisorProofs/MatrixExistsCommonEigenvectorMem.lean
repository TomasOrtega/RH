import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensor

open Matrix

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem matrix_exists_common_eigenvector_mem :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (S : Set (Matrix (Fin n) (Fin n) K)),
      (∀ A ∈ S, ∀ B ∈ S, Commute A B) → ∀ (E : Submodule K (Fin n → K)), E ≠ ⊥ →
      (∀ A ∈ S, ∀ v ∈ E, A *ᵥ v ∈ E) → ∃ v ∈ E, v ≠ 0 ∧ ∀ A ∈ S, ∃ μ : K, A *ᵥ v = μ • v := by
  intro K _ _ n S hS E hE hst
  obtain ⟨v, hvE, hv0, hv⟩ := exists_common_eigenvector_mem (K := K) (V := Fin n → K)
    (fun A : S => Matrix.toLin' (A : Matrix (Fin n) (Fin n) K))
    (fun i j v => by
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
      rw [(hS i i.2 j j.2).eq])
    E hE (fun i v hv => by simpa [Matrix.toLin'_apply] using hst i i.2 v hv)
  refine ⟨v, hvE, hv0, fun A hA => ?_⟩
  obtain ⟨l, hl⟩ := hv ⟨A, hA⟩
  exact ⟨l, by simpa [Matrix.toLin'_apply] using hl⟩

end GlobalTheory
