import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.SchurLine

open Polynomial Matrix

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Consider separately whether the proposition holds or fails. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.Det.signLemma :
    ∀ {K G ι : Type} [Field K] [Group G] [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι K) (σ : G →* G) (μ : G → K)
    (B : Matrix ι ι K), Submodule.span K (Set.range ρ) = ⊤ → (∀ s, σ (σ s) = s) → (∀ s, μ (σ s) = μ s) → IsUnit B →
    (∀ s, (ρ s)ᵀ * B * ρ (σ s) = μ s • B) → Bᵀ = B ∨ Bᵀ = -B := by
  intro K G ι _ _ _ _ ρ σ μ B hspan hσ hμ hB hlaw
  have hlaw' : ∀ s, (ρ s)ᵀ * Bᵀ * ρ (σ s) = μ s • Bᵀ := by
    intro s
    have h := congrArg Matrix.transpose (hlaw (σ s))
    rw [hσ, hμ, transpose_mul, transpose_mul, transpose_transpose, transpose_smul] at h
    rw [Matrix.mul_assoc]
    exact h
  obtain ⟨C, hC⟩ : ∃ C : Matrix ι ι K, Bᵀ = B * C := by
    obtain ⟨u, rfl⟩ := hB
    exact ⟨((u⁻¹ : (Matrix ι ι K)ˣ) : Matrix ι ι K) * (↑u : Matrix ι ι K)ᵀ, by rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]⟩
  have hcomm : ∀ t, C * ρ t = ρ t * C := by
    intro t
    have h1 := hlaw (σ t)
    have h2 := hlaw' (σ t)
    rw [hσ] at h1 h2
    have hA : IsUnit ((ρ (σ t))ᵀ * B) := by
      refine IsUnit.mul ?_ hB
      rw [Matrix.isUnit_transpose]
      exact (Group.isUnit (σ t)).map ρ
    apply hA.mul_left_cancel
    rw [← Matrix.mul_assoc _ (ρ t) C, h1, Matrix.smul_mul, ← hC, ← h2, hC]
    simp only [Matrix.mul_assoc]
  have hall : ∀ M : Matrix ι ι K, C * M = M * C := by
    intro M
    have hM : M ∈ Submodule.span K (Set.range ρ) := by rw [hspan]; trivial
    induction hM using Submodule.span_induction with
    | mem x hx => obtain ⟨t, rfl⟩ := hx; exact hcomm t
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, hx, hy]
    | smul a x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul, hx]
  obtain ⟨c, hc⟩ : C ∈ Set.range (Matrix.scalar ι) :=
    Matrix.mem_range_scalar_of_commute_single (fun i j _ => (hall _).symm)
  have hBc : Bᵀ = c • B := by
    rw [hC, ← hc]
    ext i j
    simp [Matrix.mul_diagonal, mul_comm]
  have h2 : B = (c * c) • B := by
    have h := congrArg Matrix.transpose hBc
    rw [transpose_transpose, transpose_smul, hBc, smul_smul] at h
    exact h
  by_cases hcc : c * c = 1
  · rcases mul_self_eq_one_iff.mp hcc with h | h
    · left; rw [hBc, h, one_smul]
    · right; rw [hBc, h, neg_one_smul]
  · have h0 : B = 0 := by
      have h3 : (1 - c * c) • B = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
      rcases smul_eq_zero.mp h3 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hcc
      · exact h
    left; rw [h0, transpose_zero]
