import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PiNonunit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.SelMain

noncomputable section
open Matrix

namespace PI.SqPair.LCP

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem pair_selection : Select := by
  intro R _ _ R₀ ϖ hI ι _ _ A A' h k hP hNB
  have := hI.dom
  obtain ⟨⟨_, hA⟩, ⟨_, hA'⟩, hrel⟩ := hP
  have hne : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hNB ⟨1, by simp, by ext i; exact (IsEmpty.false i).elim⟩
  let σ : R ≃+* R := starRingAut
  have hct : ∀ M : Matrix ι ι R, (M.map σ)ᵀ = Mᴴ := by
    intro M; ext i j; simp [σ, Matrix.conjTranspose_apply]
  have hs : ∀ x : ι → R, star x = fun l => σ (x l) := by
    intro x; ext l; simp [σ]
  have hσϖ : σ ϖ = ϖ := by simpa [σ] using (hI.fix ϖ).mp hI.pi_mem
  have hrel' : (h.map σ)ᵀ * A * h = ϖ ^ (2 * k) • A' := by rw [hct]; exact hrel
  obtain ⟨m, h₁, rfl, hle, _, hcase⟩ :=
    sel_main σ ϖ hI.pi_ne hI.pi_nonunit hσϖ hI.val A A' h hA hA' k hrel'
  rcases hcase with ⟨hmk, hu⟩ | ⟨hlt, g₁, j, y, _, _, _, hxy, hxx, hy⟩
  · exact absurd ⟨h₁, hu, by rw [hmk]⟩ hNB
  · refine ⟨k - m, h₁ *ᵥ Pi.single j 1, y, by omega, by omega, ?_, ⟨A' j j, ?_⟩,
      ⟨Pi.single j 1, ?_⟩, ⟨g₁ *ᵥ y, ?_⟩⟩
    · unfold hf; rw [hs]; exact hxy
    · unfold hf; rw [hs]; exact hxx
    · rw [Matrix.smul_mulVec, show k - (k - m) = m by omega]
    · rw [Matrix.smul_mulVec, ← hy, smul_smul, ← pow_add]
      congr 2
      omega

end PI.SqPair.LCP
