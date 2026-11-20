import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirLeTensorOperatorRaiseStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem kUnit_of_isUnitary_proj {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (h : IsUnitary ε E) : KUnit ε E := by
  intro a b hab u v
  have := h a b u v
  simpa [Formalism.REAL.sgn, hab] using this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation.

Reduce the conclusion to the remaining proof obligations. Check the signs of the components of the expression. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Apply the first step, then apply the next step to every resulting obligation. Simplify the hypotheses and the goal together. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem casKLe_proj_single : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε E c w → ∀ s d, CasKLe ε (F s) (c + Real.sqrt n) (pr s (Pi.single d w)) := by
  intro M _ _ n ε E N _ _ F io pr c w hE hF hT hc hw s d
  have key := GlobalTheory.T.compactCasimirLe_tensorOperator_raise M n ε E (N s) (Fin n) (F s)
    (fun j => (pr s) ∘ₗ (LinearMap.single ℂ (fun _ : Fin n => M) j))
    (fun a b => Matrix.of fun i j => if i = b ∧ j = a then (-1 : ℂ) else 0) c (Real.sqrt n)
    (kUnit_of_isUnitary_proj hE) (kUnit_of_isUnitary_proj (hF s)) hc (Real.sqrt_nonneg _) ?_ ?_ ?_ w hw d
  · simpa using key
  · intro a b _
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases h : i = a ∧ j = b
    · simp [h.1, h.2]
    · have h' : ¬ (j = b ∧ i = a) := fun h2 => h ⟨h2.2, h2.1⟩
      simp [h, h']
  · intro x
    rw [Real.sq_sqrt (Nat.cast_nonneg n), Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h1 : ∀ b : Fin n, ∑ i, ‖∑ j, (Matrix.of fun i j => if i = b ∧ j = a then (-1 : ℂ) else 0) i j • x j‖ ^ 2
        = ‖x a‖ ^ 2 := by
      intro b
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single a]
        · simp
        · intro j _ hj; simp [hj]
        · simp
      · intro i _ hi; simp [hi]
      · simp
    calc _ ≤ ∑ _b : Fin n, ‖x a‖ ^ 2 := by
          refine Finset.sum_le_sum fun b _ => ?_
          split_ifs
          · exact (h1 b).le
          · positivity
      _ = _ := by simp
  · intro a b _ j v
    simp only [LinearMap.comp_apply, LinearMap.single_apply, Matrix.of_apply]
    rw [← hT.pr_comm]
    simp only [← map_smul, ← map_sum, ← map_add]
    congr 1
    funext i
    rw [Finset.sum_eq_single b]
    · simp only [dualTens, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
      by_cases h1 : i = j <;> by_cases h2 : i = b <;> by_cases h3 : j = a <;>
        simp_all [sub_eq_add_neg, eq_comm]
    · intro k _ hk; simp [hk]
    · simp

end GlobalTheory
