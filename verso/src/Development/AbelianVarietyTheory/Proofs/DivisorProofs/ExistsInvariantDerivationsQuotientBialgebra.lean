import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationOfCounitalComul
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Proceed by induction.

Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Treat this case separately.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem quotient_base_change_invariant_derivations :
    ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] (I : Ideal O) (d : ℕ) (l : Fin d → (A →ₗ[O] O ⧸ I)), (∀ i a b, l i (a * b) = Coalgebra.counit (R := O) a • l i b + Coalgebra.counit (R := O) b • l i a) → ∃ D : Fin d → Derivation (O ⧸ I) ((O ⧸ I) ⊗[O] A) ((O ⧸ I) ⊗[O] A), ∀ i a, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] A) (D i (1 ⊗ₜ a)) = l i a := by
  intro O A _ _ _ I d l hl
  set S := O ⧸ I
  set B := S ⊗[O] A
  let ε := Bialgebra.counitAlgHom S B
  let Δ := Bialgebra.comulAlgHom S B
  have hεt : ∀ (s : S) (a : A), ε (s ⊗ₜ a) = Coalgebra.counit (R := O) a • s := by
    intro s a
    show Coalgebra.counit (R := S) (s ⊗ₜ[O] a) = _
    rw [TensorProduct.counit_tmul]
    rfl
  have hε : (∀ b : B, TensorProduct.lid S B (LinearMap.rTensor B ε.toLinearMap (Δ b)) = b) ∧
      (∀ b : B, TensorProduct.rid S B (LinearMap.lTensor B ε.toLinearMap (Δ b)) = b) := by
    constructor
    · intro b
      have := Coalgebra.rTensor_counit_comul (R := S) b
      show TensorProduct.lid S B (LinearMap.rTensor B Coalgebra.counit (Coalgebra.comul b)) = b
      rw [this]; simp
    · intro b
      have := Coalgebra.lTensor_counit_comul (R := S) b
      show TensorProduct.rid S B (LinearMap.lTensor B Coalgebra.counit (Coalgebra.comul b)) = b
      rw [this]; simp
  have key : ∀ i, ∃ D : Derivation S B B, ∀ b, ε (D b) = LinearMap.liftBaseChange S (l i) b := by
    intro i
    refine invariant_derivation_exists S B ε Δ hε (LinearMap.liftBaseChange S (l i)) ?_
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul t c =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hεt, hεt]
        rw [LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
          LinearMap.liftBaseChange_tmul, hl]
        simp only [smul_eq_mul, smul_add, Algebra.smul_def]
        ring
      | add y₁ y₂ ih₁ ih₂ =>
        rw [mul_add, map_add, ih₁, ih₂, map_add, map_add]
        ring
    | add x₁ x₂ ih₁ ih₂ =>
      rw [add_mul, map_add, ih₁, ih₂, map_add, map_add]
      ring
  choose D hD using key
  refine ⟨D, fun i a => ?_⟩
  rw [hD, LinearMap.liftBaseChange_tmul, one_smul]

end GlobalTheory
