import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
open GlobalTheory.UnitLemma Polynomial Matrix

namespace GlobalTheory.InertUnitOrb

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem conj_of_norm_class (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ)
    (γ γ' : Matrix (Fin n) (Fin n) K.E) (x x' v : B.Aˣ) (ψ ψ' : B.A ≃ₗ[K.E] (Fin n → K.E))
    (h : GlobalTheory.InertUnitOrb.IsModel B γ x ψ) (h' : GlobalTheory.InertUnitOrb.IsModel B γ' x' ψ')
    (hx : (x' : B.A) = x * (v * B.σ v)) :
    ∃ u : Matrix (Fin n) (Fin n) K.E, (u.map K.c)ᵀ * u = 1 ∧ γ * u = u * γ' := by
  obtain ⟨-, hg, hh⟩ := h
  obtain ⟨-, hg', hh'⟩ := h'
  set f : (Fin n → K.E) →ₗ[K.E] (Fin n → K.E) :=
    ψ.toLinearMap ∘ₗ LinearMap.mulLeft K.E (v : B.A) ∘ₗ ψ'.symm.toLinearMap with hf
  have key : ∀ a b, stdH K n (f a) (f b) = stdH K n a b := by
    intro a b
    obtain ⟨y, rfl⟩ := ψ'.surjective a
    obtain ⟨z, rfl⟩ := ψ'.surjective b
    simp only [hf, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.mulLeft_apply]
    rw [hh, hh', hx]
    unfold InvAlg.herm
    congr 1
    rw [map_mul]
    ring
  refine ⟨LinearMap.toMatrix' f, ?_, ?_⟩
  · ext i j
    have k := key (Pi.single j 1) (Pi.single i 1)
    simp only [stdH] at k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, LinearMap.toMatrix'_apply,
      Matrix.one_apply]
    rw [show (∑ x, K.c (f (Pi.single i 1) x) * f (Pi.single j 1) x)
        = ∑ x, f (Pi.single j 1) x * K.c (f (Pi.single i 1) x) from
        Finset.sum_congr rfl fun _ _ => mul_comm _ _, k]
    simp [Pi.single_apply, eq_comm]
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun a => ?_
    obtain ⟨y, rfl⟩ := ψ'.surjective a
    simp only [hf, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.mulLeft_apply, Matrix.toLin'_apply]
    rw [← hg, ← hg', LinearEquiv.symm_apply_apply, ← mul_assoc, ← mul_assoc, mul_comm B.g]

end GlobalTheory.InertUnitOrb
