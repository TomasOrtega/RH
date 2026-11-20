import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
open GlobalTheory.UnitLemma Polynomial Matrix

noncomputable section

namespace GlobalTheory.ModelCharpoly
open GlobalTheory.InertUnitOrb

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem charpoly_eq (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E)
    (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (h : ∀ y, ψ (B.g * y) = γ *ᵥ ψ y) : γ.charpoly = B.P := by
  let b : Module.Basis (Fin n) K.E B.A := (Pi.basisFun K.E (Fin n)).map ψ.symm
  have hm : LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g) = γ := by
    ext i j
    simp [b, LinearMap.toMatrix_apply, h]
  rw [InvAlg.P, ← LinearMap.charpoly_toMatrix (LinearMap.mulLeft K.E B.g) b, hm]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. By extensionality, compare the relevant components. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts.
-/
theorem unitary (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E)
    (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (h : ∀ y, ψ (B.g * y) = γ *ᵥ ψ y)
    (hh : ∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) (hg : B.g * B.σ B.g = 1) :
    (γ.map K.c)ᵀ * γ = 1 := by
  have key : ∀ a b : Fin n → K.E, stdH K n (γ *ᵥ a) (γ *ᵥ b) = stdH K n a b := by
    intro a b
    obtain ⟨y, rfl⟩ := ψ.surjective a
    obtain ⟨z, rfl⟩ := ψ.surjective b
    rw [← h, ← h, hh, hh, InvAlg.herm, InvAlg.herm]
    congr 1
    rw [map_mul B.σ]
    calc (x : B.A) * (B.g * y) * (B.σ B.g * B.σ z) = (x : B.A) * y * B.σ z * (B.g * B.σ B.g) := by ring
      _ = _ := by rw [hg, mul_one]
  ext i j
  have := key (Pi.single j 1) (Pi.single i 1)
  simp [stdH, Matrix.mulVec_single, Pi.single_apply, Matrix.mul_apply, Matrix.one_apply, mul_comm] at this
  simp [Matrix.mul_apply, Matrix.one_apply]
  simpa [mul_comm, eq_comm] using this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem model_charpoly_unitary : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K.E) (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)),
    GlobalTheory.InertUnitOrb.IsModel B γ x ψ → γ.charpoly = B.P ∧ (B.g * B.σ B.g = 1 → (γ.map K.c)ᵀ * γ = 1) := by
  intro K B n γ x ψ hM
  exact ⟨charpoly_eq K B n γ ψ hM.2.1, unitary K B n γ x ψ hM.2.1 hM.2.2⟩

end GlobalTheory.ModelCharpoly

end
