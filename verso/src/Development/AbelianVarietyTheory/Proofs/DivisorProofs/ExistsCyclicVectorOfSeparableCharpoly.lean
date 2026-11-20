import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
import Formalism.PadicSubsetSums.StableGradedCounts.ExistsNeZeroAevalEqZero

open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_cyclicVector_of_separable_charpoly {K : Type} [Field K] (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) :
    ∃ v₀ : Fin n → K, ∀ u : Fin n → K, ∃ p : K[X], u = aeval γ p *ᵥ v₀ := by
  have hs' : (Matrix.toLin' γ).charpoly.Separable := by rwa [Matrix.charpoly_toLin']
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.base_change_cyclic_vector K (Fin n → K) (Matrix.toLin' γ) hs'
  refine ⟨e, fun u => ?_⟩
  obtain ⟨p, hp⟩ := he u
  refine ⟨p, ?_⟩
  rw [← hp]
  have h : aeval (Matrix.toLin' γ) p = Matrix.toLin' (aeval γ p) := by
    have := (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toAlgHom γ p).symm
    exact this.symm
  rw [h, Matrix.toLin'_apply]

end GlobalTheory.LatOrb
