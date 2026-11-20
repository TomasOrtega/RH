import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Win.vvat :
    ∀ (l t : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (T b B : ℝ), 0 ≤ b → (t : ℝ) ≤ T → T * b ≤ B →
      (∀ e : ℕ, 1 ≤ e → e < t → shaInv E l e ≠ ⊤ ∧ ((shaInv E l e).toNat : ℝ) ≤ b) → VVat l E t B := by
  intro l t _ E _ _ T b B hb htT hTB h Ω _ _ _ D
  refine ⟨fun e he het => by rw [shaLen_eq_shaInv]; exact (h e he het).1, ?_⟩
  calc ∑ e ∈ Finset.Ico 1 t, ((shaLen D e).toNat : ℝ) ≤ ∑ _e ∈ Finset.Ico 1 t, b := by
        apply Finset.sum_le_sum
        intro e he
        rw [Finset.mem_Ico] at he
        rw [shaLen_eq_shaInv]
        exact (h e he.1 he.2).2
    _ = ((t - 1 : ℕ) : ℝ) * b := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ T * b := mul_le_mul_of_nonneg_right (le_trans (by exact_mod_cast Nat.sub_le t 1) htT) hb
    _ ≤ B := hTB
