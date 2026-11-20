import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Check the signs of the components of the expression. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Establish an intermediate fact.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem Vo_polyB_qs : ∀ (l : ℕ) (a : ℕ → ℂ), 0 < l → PolyB a →
    PolyB (Vo l a) ∧ ∀ τ σ : ℍ, (σ : ℂ) = l * τ → qs (Vo l a) τ = qs a σ := by
  intro l a hl ha
  refine ⟨?_, ?_⟩
  · obtain ⟨C, A, h⟩ := ha
    have hC : 0 ≤ C := by
      have := h 0
      simp at this
      exact le_trans (norm_nonneg _) this
    refine ⟨C, A, fun n => ?_⟩
    unfold Vo
    split_ifs with hd
    · refine (h (n / l)).trans ?_
      gcongr
      exact_mod_cast Nat.div_le_self n l
    · simp only [norm_zero]; positivity
  · intro τ σ hσ
    unfold qs
    have hinj : Function.Injective (fun m : ℕ => l * m) :=
      fun x y hxy => Nat.eq_of_mul_eq_mul_left hl hxy
    have hsupp : Function.support (fun n : ℕ => Vo l a n * cexp (2 * π * Complex.I * n * τ)) ⊆
        Set.range (fun m : ℕ => l * m) := by
      intro n hn
      by_contra hr
      apply hn
      have : ¬ l ∣ n := by
        rintro ⟨m, rfl⟩
        exact hr ⟨m, rfl⟩
      simp [Vo, this]
    rw [← hinj.tsum_eq hsupp]
    congr 1
    ext m
    have hl' : l ≠ 0 := hl.ne'
    simp only [Vo, dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl, hσ]
    congr 2
    push_cast
    ring

end GlobalTheory.EisM
