import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd

namespace GlobalTheory

/- English proof (translation)
Introduce `h k M hM`. Take `⟨N, hN⟩` from `symplecticGroupMap_zmod_surjective (Fin h) k ⟨M, hM⟩`. Use `⟨N.1, N.2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hN` as an intermediate fact. Rewrite `this` using `[coe_symplecticGroupMap]`.

Simplify using `using this`.
-/
theorem symplectic_zmod_lift : ∀ (h k : ℕ) (M : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) (ZMod k)),
    M ∈ Matrix.symplecticGroup (Fin h) (ZMod k) → ∃ N : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) ℤ,
      N ∈ Matrix.symplecticGroup (Fin h) ℤ ∧ N.map (Int.cast : ℤ → ZMod k) = M := by
  intro h k M hM
  obtain ⟨N, hN⟩ := symplecticGroupMap_zmod_surjective (Fin h) k ⟨M, hM⟩
  refine ⟨N.1, N.2, ?_⟩
  have := congrArg Subtype.val hN
  rw [coe_symplecticGroupMap] at this
  simpa using this

end GlobalTheory
